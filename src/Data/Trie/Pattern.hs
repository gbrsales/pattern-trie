-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at http://mozilla.org/MPL/2.0/.

{-# LANGUAGE DeriveGeneric
           , DeriveAnyClass
           , GeneralizedNewtypeDeriving
           , DerivingStrategies
           , BangPatterns
           , TupleSections
#-}

-- | A variant of a (radix) trie with the following characteristics:
--
--   * Keys are 'Pattern's composed of 'Matcher's and hence a single key
--     can match multiple input 'Str'ings.
--   * Keys are understood as being composed of (indivisible) chunks of
--     'ByteString's. More precisely, every chunk of an input 'Str'ing is
--     tested against a 'Matcher' of a 'Pattern' in full. As a result,
--     pattern tries usually end up less compact than more general tries,
--     since sharing of prefixes is limited to the granularity of these
--     chunks.
--   * Matching a 'Str'ing on a trie can 'Capture' parts of the string.
--
-- These characteristics hint at the primary intended use-case, whereby
-- keys have a "natural" decomposition into chunks and the same
-- chunks are heavily shared by different keys, e.g. as in directory trees.
-- A pattern trie allows to associate values with such patterns, whereby a
-- single value can essentially be looked up by all strings matching a pattern,
-- thereby capturing parts of it. Such a trie can thus form the basis of e.g. a
-- web server routing mechanism for dispatching requests to handler functions
-- together with captured parameters, based on the request path in the URL.
--
-- __Strictness:__
-- A 'Trie' is strict in the spine as well as the values (WHNF).
--
-- __Ordering:__ The order of keys and thus elements is unspecified.
-- No particular order may be assumed by folds and traversals, whose
-- combining operations should hence be commutative.
--
-- __Example:__
--
-- >>> :set -XOverloadedStrings
--
-- >>> let p1 = mempty |> EqStr "home" |> EqStr "alice" |> EqStr "tmp"
-- >>> let p2 = mempty |> EqStr "home" |> AnyStr        |> EqStr "music"
-- >>> let p3 = mempty |> EqStr "data" |> EqStr "bob"   |> EqStr "books"
-- >>> let p4 = mempty |> EqStr "data" |> AnyStr        |> EqStr "books"
-- >>> let p5 = mempty |> EqStr "data" |> AnyStr        |> EqStr "books" |> EqStr "sicp"
--
-- >>> let trie = fromAssocList $ [p1,p2,p3,p4,p5] `zip` [1..] :: Trie Int
--
-- >>> match ["home","alice","tmp"] trie
-- Just (1,fromList [])
--
-- >>> match ["home","bob","tmp"] trie
-- Nothing
--
-- >>> match ["home","alice","music"] trie
-- Just (2,fromList [Capture {captured = "alice"}])
--
-- >>> match ["home","bob","music"] trie
-- Just (2,fromList [Capture {captured = "bob"}])
--
-- >>> match ["data","bob","books"] trie
-- Just (3,fromList [])
--
-- >>> match ["data","alice","books"] trie
-- Just (4,fromList [Capture {captured = "alice"}])
--
-- >>> match ["data","alice","books","sicp"] trie
-- Just (5,fromList [Capture {captured = "alice"}])
--
-- >>> match ["data","bob","books","sicp"] trie
-- Just (5,fromList [Capture {captured = "bob"}])
--
-- >>> matchPrefix ["data","alice","books","wonderland"] trie
-- Just (4,fromList [Capture {captured = "alice"}],["wonderland"])
--
-- >>> matchPrefix ["data","bob","books","wonderland"] trie
-- Just (4,fromList [Capture {captured = "bob"}],["wonderland"])
--
-- >>> let (t,c,s) = matchPrefixTrie ["data","bob","books","wonderland"] trie
-- >>> (value t, c, s)
-- (Just 4,fromList [Capture {captured = "bob"}],["wonderland"])
--
module Data.Trie.Pattern
    ( Trie, value

    -- * Patterns
    , Pattern, Str, Matcher (..)
    , apply, capture, (|>)
    , Capture, captured

    -- * List conversion
    , fromAssocList
    , toAssocList

    -- * Modifications
    , insert
    , adjust
    , delete

    -- * 'Pattern' lookup
    , lookup
    , lookupPrefix
    , lookupPrefixTrie

    -- * 'Str'ing matching
    , match
    , matchPrefix
    , matchPrefixTrie

    -- * Special folds and traversals
    , traverseWithKey
    , foldMapWithKey
    , foldrWithKey
    ) where

import GHC.Generics (Generic)

import Control.Applicative
import Control.DeepSeq (NFData)
import Control.Monad ((<$!>))
import Data.ByteString (ByteString)
import Data.Foldable
import Data.List (foldl')
import Data.HashMap.Strict (HashMap)
import Data.Maybe (fromMaybe)
import Data.Semigroup
import Data.Sequence (Seq (..), (|>))
import Prelude hiding (lookup)

import qualified Data.HashMap.Strict as HashMap
import qualified Data.Sequence       as Seq
import qualified Data.Traversable    as Traversable

-- | A mapping from 'Pattern's to values of type 'a'.
data Trie a = Trie
    { strtries :: !(HashMap ByteString (Trie a))
    , vartrie  :: !(Maybe (Trie a))
    , value    :: !(Maybe a)
        -- ^ The value at the root of the trie, i.e.
        --
        -- @
        -- value t == 'lookup' mempty t
        -- @
    } deriving stock (Eq, Show, Read, Generic)
      deriving anyclass NFData

instance Traversable Trie where
    traverse f = traverseWithKey (const f)

instance Functor Trie where
    fmap = Traversable.fmapDefault

instance Foldable Trie where
  foldMap = Traversable.foldMapDefault

  null (Trie a Nothing Nothing) = HashMap.null a
  null _                        = False
  {-# INLINE null #-}

-- | /Note (left preference)/: If two tries have a value attached to
-- the same 'Pattern' (i.e. to the same key), then @t1 <> t2@ preserves
-- the value of @t1@.
instance Semigroup (Trie a) where
    a <> b =  Trie (HashMap.unionWith (<>) (strtries a) (strtries b))
                   (vartrie a <> vartrie b)
                   (value a <|> value b)

    stimes = stimesIdempotent

-- | /Note/: @mappend = (<>)@.
instance Monoid (Trie a) where
    mempty  = Trie mempty Nothing Nothing
    mappend = (<>)

-----------------------------------------------------------------------------
-- Patterns

-- | A pattern is a sequence of 'Matcher's and serves as a key
-- in a pattern trie.
--
-- __Overlapping Patterns:__
-- Two patterns @p@ and @p'@ with @p /= p'@, are /overlapping/ if there exists
-- an input 'Str'ing that is (fully) 'match'ed by both patterns. In that case,
-- for the input string in question, the preference is given by the partial
-- order @EqStr > AnyStr@ on the competing matchers, i.e. towards the more
-- specific pattern. For an input string with a proper prefix matching the
-- overlapping patterns, the preference is reversed, i.e. towards the more
-- general pattern. That is, in the latter case a 'match' naturally yields
-- 'Nothing', whereas 'matchPrefix' will match the more general pattern,
-- yielding the associated value and excess input.
type Pattern = Seq Matcher

-- | A (chunked) input string to 'match' on a 'Pattern' in a trie.
--
-- /Note:/ Input strings can be infinite. Since the tries are always finite,
-- an infinite input string is only consumed until either a match has been
-- found or the applicable paths in the trie have been exhaustively searched.
type Str = [ByteString]

-- | A captured chunk of an input 'Str'ing.
newtype Capture = Capture { captured :: ByteString }
    deriving stock (Eq, Ord, Show, Read, Generic)
    deriving anyclass NFData

-- | A 'Matcher' is applied on a single chunk of an input 'Str'ing
-- while looking for a 'match' and either /succeeds/ or /fails/. If it succeeds,
-- it may additionally capture (part of) the chunk.
data Matcher
    -- | Match and capture an arbitrary chunk of an input string.
    = AnyStr
    -- | Match a chunk of an input string exactly, capturing nothing.
    | EqStr !ByteString
    deriving (Eq, Show, Read)

-- | Directly apply a 'Str'ing to a 'Pattern', returning the unmatched
-- suffix of the pattern together with the captured chunks and the
-- remaining (unmatched) suffix of the input string.
apply :: Str -> Pattern -> (Pattern, Seq Capture, Str)
apply = go Seq.empty
  where
    go !cs ss Empty = (Empty, cs, ss)
    go !cs [] p     = (p    , cs, [])
    go !cs str@(s:s') pat@(m :<| p') = case m of
        AnyStr   -> go (cs |> Capture s) s' p'
        EqStr ss -> if s == ss
            then go cs s' p'
            else (pat, cs, str)

-- | Like 'apply' but only returns the captures.
capture :: Str -> Pattern -> Seq Capture
capture s p = case apply s p of
    (_, c, _) -> c
{-# INLINE capture #-}

-----------------------------------------------------------------------------
-- List conversion

-- | Create a pattern trie from a list of patterns and associated values.
fromAssocList :: [(Pattern, a)] -> Trie a
fromAssocList = foldl' add mempty
  where
    add t (p, a) = insert p a t

-- | Create a list of patterns and associated values from a pattern trie.
toAssocList :: Trie a -> [(Pattern, a)]
toAssocList t = foldrWithKey (\p a l -> (p, a) : l) [] t

-----------------------------------------------------------------------------
-- Updates

-- | Insert the value for the given pattern into the trie.
insert :: Pattern -> a -> Trie a -> Trie a
insert p !a = go p
  where
    go Empty            = modVal (const (Just a))
    go (AnyStr  :<| p') = modVar ((Just $!) . go p' . fromMaybe mempty)
    go (EqStr s :<| p') = modStr $ \m ->
        let t' = fromMaybe mempty (HashMap.lookup s m)
        in HashMap.insert s (go p' t') m

-- | Update the value of the given pattern in the trie, if it exists.
adjust :: Pattern -> (a -> a) -> Trie a -> Trie a
adjust p f = go p
  where
    go Empty            = modVal (f <$!>)
    go (AnyStr  :<| p') = modVar (go p' <$!>)
    go (EqStr s :<| p') = modStr (HashMap.adjust (go p') s)

-- | Remove the value for the given pattern from the trie, if it exists.
delete :: Pattern -> Trie a -> Trie a
delete p = go p
  where
    go Empty            = modVal (const Nothing)
    go (AnyStr  :<| p') = modVar (maybe Nothing (go' p'))
    go (EqStr s :<| p') = modStr (HashMap.update (go' p') s)

    go' p' t = case go p' t of
        t' | null t' -> Nothing
        t'           -> Just t'

-----------------------------------------------------------------------------
-- Lookups

type LookupNextR r a = Trie a -> Pattern -> r -> r

lookupIter :: LookupNextR r a -> r -> Pattern -> Trie a -> r
lookupIter nextR = go
  where
    go r p t =
        let !r' = nextR t p r
        in case p of
            Empty          -> r'
            AnyStr  :<| p' -> maybe r' (go r' p') (vartrie t)
            EqStr s :<| p' -> maybe r' (go r' p') (HashMap.lookup s (strtries t))
{-# INLINE lookupIter #-}

-- | Lookup the trie rooted at the longest prefix of a pattern for which
-- there are values in the trie, returning it together with the remaining
-- suffix of the pattern.
lookupPrefixTrie :: Pattern -> Trie a -> (Trie a, Pattern)
lookupPrefixTrie p t = lookupIter nextR (t, Empty) p t
  where
    nextR t' p' = const (t', p')

-- | Lookup the value for the longest matching prefix of a pattern,
-- returning it together with the remaining suffix of the pattern.
-- If there is no value in the trie for any prefix of the given pattern,
-- the result is 'Nothing'.
lookupPrefix :: Pattern -> Trie a -> Maybe (a, Pattern)
lookupPrefix p t = lookupIter nextR Nothing p t
  where
    nextR t' p' r = ((,p') <$!> value t') <|> r

-- | Lookup the value of a pattern.
-- If there is no value in the trie for the given pattern, the result is
-- 'Nothing'.
lookup :: Pattern -> Trie a -> Maybe a
lookup p t = case lookupPrefixTrie p t of
    (t', Empty) -> value t'
    _           -> Nothing
{-# INLINE lookup #-}

-----------------------------------------------------------------------------
-- Matching

-- | A choice point for backtracking to alternative branches.
data Choice a = Choice !(Seq Capture) Str !(Trie a)

type MatchNextR r a = Trie a -> Seq Capture -> Str -> r -> r

matchIter :: MatchNextR r a -> r -> Str -> Trie a -> r
matchIter nextR = go Seq.empty []
  where
    go !cs !cps r str t =
        let !r' = nextR t cs str r
        in case str of
            []     -> r'
            (s:s') -> case HashMap.lookup s (strtries t) of
                Just t' -> case vartrie t of
                    Nothing  -> go cs cps r' s' t'
                    Just t'' ->
                        -- Add a new choice point
                        let cps' = Choice (cs |> Capture s) s' t'' : cps
                        in go cs cps' r' s' t'
                Nothing -> case vartrie t of
                    Just t' -> go (cs |> Capture s) cps r' s' t'
                    -- Continue at the last choice point, if any
                    Nothing -> case cps of
                        []                         -> r'
                        (Choice cs' ss' t' : cps') -> go cs' cps' r' ss' t'
{-# INLINE matchIter #-}

-- | Lookup the trie rooted at the longest matching prefix of the input string
-- for which there are values in the trie, returning it together with
-- any captured parts and the remaining (unmatched) suffix of the input string.
matchPrefixTrie :: Str -> Trie a -> (Trie a, Seq Capture, Str)
matchPrefixTrie s t = matchIter nextR (t, Seq.empty, []) s t
  where
    nextR t' cs' s' = const (t', cs', s')

-- | Lookup the value for the longest matching prefix of the input string,
-- returning it together with any captured parts and the remaining
-- (unmatched) suffix of the input string. If no prefix of the input
-- string matches any pattern in the trie, the result is 'Nothing'.
matchPrefix :: Str -> Trie a -> Maybe (a, Seq Capture, Str)
matchPrefix s t = matchIter nextR Nothing s t
  where
    nextR t' cs s' r = ((,cs,s') <$!> value t') <|> r

-- | Lookup the value for an input string by matching it against the patterns of
-- a trie. The value of the matching pattern, if any, is returned together with
-- any captured parts of the input string. If the input string does not match
-- any pattern in the trie, the result is 'Nothing'.
match :: Str -> Trie a -> Maybe (a, Seq Capture)
match s t = case matchPrefixTrie s t of
    (t', cs, []) -> (,cs) <$> value t'
    _            -> Nothing
{-# INLINE match #-}

-----------------------------------------------------------------------------
-- Folds and traversals with keys (patterns)

traverseWithKey :: Applicative f => (Pattern -> a -> f b) -> Trie a -> f (Trie b)
traverseWithKey f t = go mempty t
  where
    go !p (Trie vals vars v) =
        let f1 = HashMap.traverseWithKey (\k -> go (p |> EqStr k)) vals
            f2 = traverse (go (p |> AnyStr)) vars
            f3 = traverse (f p) v
        in Trie <$> f1 <*> f2 <*> f3

foldMapWithKey :: Monoid m => (Pattern -> a -> m) -> Trie a -> m
foldMapWithKey f = getConst . traverseWithKey (\p -> Const . f p)

foldrWithKey :: (Pattern -> a -> b -> b) -> b -> Trie a -> b
foldrWithKey f b t = appEndo (foldMapWithKey (\p -> Endo . f p) t) b

-----------------------------------------------------------------------------
-- Utilities

modStr :: (HashMap ByteString (Trie a) -> HashMap ByteString (Trie a)) -> Trie a -> Trie a
modStr f t = t { strtries = f (strtries t) }
{-# INLINE modStr #-}

modVar :: (Maybe (Trie a) -> Maybe (Trie a)) -> Trie a -> Trie a
modVar f t = t { vartrie = f (vartrie t) }
{-# INLINE modVar #-}

modVal :: (Maybe a -> Maybe a) -> Trie a -> Trie a
modVal f t = t { value = f (value t) }
{-# INLINE modVal #-}

