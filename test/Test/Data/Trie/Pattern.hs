-- This Source Code Form is subject to the terms of the Mozilla Public
-- License, v. 2.0. If a copy of the MPL was not distributed with this
-- file, You can obtain one at http://mozilla.org/MPL/2.0/.

{-# LANGUAGE CPP #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections #-}

module Test.Data.Trie.Pattern (tests) where

import Control.Monad
import Data.ByteString (ByteString)
import Data.Foldable
import Data.Functor.Identity
import Data.Functor.Compose
import Data.List (inits)
#if __GLASGOW_HASKELL__ < 804
import Data.Semigroup
#endif
import Data.Sequence (Seq (..))
import Data.Trie.Pattern
import Test.Tasty
import Test.Tasty.QuickCheck

import qualified Data.ByteString.Char8 as C8
import qualified Data.Sequence         as Seq
import qualified Data.Trie.Pattern     as Trie

tests :: TestTree
tests = testGroup "Data.Trie.Pattern"
    [ testGroup "Semigroup"
        [ testProperty "Left preference" checkSemigroupLeftPref
        , testProperty "Associativity" checkSemigroupAssoc
        ]
    , testGroup "Monoid"
        [ testProperty "Identity" checkMonoidId
        ]
    , testGroup "Functor"
        [ testProperty "Identity" checkFunctorId
        , testProperty "Composition" checkFunctorComp
        ]
    , testGroup "Traversable"
        [ testProperty "Identity" checkTraversableId
        , testProperty "Composition" checkTraversableComp
        ]
    , testProperty "capture" checkCapture
    , testProperty "match" checkMatch
    , testProperty "match (overlapping)" checkMatchOverlapping
    , testProperty "match (partial overlap)" checkMatchPartialOverlap
    , testProperty "lookup" checkLookup
    , testProperty "insert" checkInsert
    , testProperty "from/to list" checkListConversion
    , testProperty "delete" checkDelete
    , testProperty "adjust" checkAdjust
    , testProperty "null" checkNull
    , testProperty "value" checkValue
    , testProperty "lookupPrefix" checkLookupPrefix
    , testProperty "matchPrefix" checkMatchPrefix
    ]

-------------------------------------------------------------------------------
-- Basic properties

checkNull :: Property
checkNull = once (null (mempty :: Trie ByteString Int))
    .&&. (forAll genTrie (not . null))

checkValue :: Property
checkValue = forAll genTrie $ \t ->
    Trie.value t == Trie.lookup Empty t

checkListConversion :: Property
checkListConversion = forAll genTrie $ \t ->
    Trie.fromAssocList (Trie.toAssocList t) == t

checkCapture :: Property
checkCapture = forAll genPatternWithStr $ \(p, s) ->
    Trie.unapplyCapture p (Trie.applyCapture s p) == s

-------------------------------------------------------------------------------
-- Properties of lookups and matching

checkMatch :: Property
checkMatch = forAll genPatterns check
  where
    check patterns =
        let t = Trie.fromAssocList patterns
        in conjoin . flip map patterns $ \(p, a) ->
            forAll (genStr p) $ \s ->
                let c = Trie.applyCapture s p
                in Trie.match s t == Just (a, c)

checkMatchOverlapping :: Property
checkMatchOverlapping = forAll genPatternWithStr $ \(p, s) ->
    let -- Overlaps with 'p' w.r.t 's'
        p' = Seq.fromList (map Trie.EqStr s)
        t  = Trie.fromAssocList [(p, 1), (p', 2)] :: Trie ByteString Int
    in
        Trie.match s t == Just (2, Seq.empty)

-- Partially overlapping patterns (i.e. those with an overlapping
-- proper prefix) are not ambiguous but require backtracking via
-- choice points, since the more specific path is explored first.
checkMatchPartialOverlap :: Property
checkMatchPartialOverlap = forAll genPatternWithStr $ \(p, s) ->
    let -- A match for ../a/c requires backtracking from ../a/b
        -- to the choice point before ../a
        pm  = p |> AnyStr    |> EqStr "c" -- matches
        p'  = p |> EqStr "a" |> EqStr "b" -- explored first, no match
        p'' = p |> EqStr "a" |> AnyStr |> AnyStr -- explored first, no match
        s'  = s ++ ["a","c"]
        t   = Trie.fromAssocList [(p',  1), (pm, 2)] :: Trie ByteString Int
        t'  = Trie.fromAssocList [(p'', 1), (pm, 2)] :: Trie ByteString Int
        c   = Trie.applyCapture s' pm
    in
        Trie.match s' t  == Just (2, c) &&
        Trie.match s' t' == Just (2, c)

checkLookup :: Property
checkLookup = forAll genPatterns check
  where
    check patterns =
        let t = Trie.fromAssocList patterns
        in conjoin . flip map patterns $ \(p, a) ->
            Trie.lookup p t == Just a

-- Generate a trie containing values for all prefixes of an
-- arbitrary pattern. Then iteratively remove the patterns
-- from the trie, starting with the longest prefix, each time
-- verifying that 'lookupPrefix' yields the right value and
-- remaining suffix.
checkLookupPrefix :: Property
checkLookupPrefix = forAll (genPattern "") $ \p ->
    let
        patterns = toList (Seq.inits p) `zip` [(1::Int)..]
        trie     = Trie.fromAssocList patterns
        check (px, a) ~(t, props) =
            let
                p' = Seq.drop (Seq.length px) p
                ok = Trie.lookupPrefix p t == Just (a, p')
            in
                (Trie.delete px t, ok : props)
    in
        conjoin (snd (foldr check (trie, []) patterns))

-- Generate a trie containing values for all prefixes of an
-- arbitrary pattern. Then iteratively remove the patterns
-- from the trie, starting with the longest prefix, each time
-- verifying that 'matchPrefix' applied to an input string
-- matching the entire pattern yields the right value, captured
-- chunks and remaining suffix.
checkMatchPrefix :: Property
checkMatchPrefix = forAll genPatternWithStr $ \(p, s) ->
    let
        patterns = toList (Seq.inits p) `zip` [(1::Int)..]
        trie     = Trie.fromAssocList patterns
        inputs   = patterns `zip` inits s
        check ((px, a), sx) ~(t, props) =
            let
                s' = drop (length sx) s
                cs = Trie.applyCapture sx px
                ok = Trie.matchPrefix s t == Just (a, cs, s')
            in
                (Trie.delete px t, ok : props)
    in
        conjoin (snd (foldr check (trie, []) inputs))

-------------------------------------------------------------------------------
-- Properties of modifications

checkInsert :: Property
checkInsert = forAll genTrie $ \t ->
    forAll (genPattern =<< genByteString) $ \p ->
        let t' = Trie.insert p 42 t
        in Trie.lookup p t' == Just 42

-- For an arbitrary trie, iteratively delete every pattern, checking
-- the presence and absence of the pattern before and after each
-- deletion, respectively, as well as that the final trie is empty.
checkDelete :: Property
checkDelete = forAll genTrie $ \t ->
    let (t', props) = Trie.foldrWithKey reduce (t, []) t
    in null t' .&&. conjoin props
  where
    reduce p a (t, props) =
        let before = Trie.lookup p t  == Just a
            t'     = Trie.delete p t
            after  = Trie.lookup p t' == Nothing
        in (t', before : after : props)

checkAdjust :: Property
checkAdjust = forAll genTrie $ \t ->
    let (p, a) = head (Trie.toAssocList t)
        t' = Trie.adjust p (+ 1) t
    in Trie.lookup p t' == Just (a + 1)     &&
       Trie.delete p t  == Trie.delete p t'

-------------------------------------------------------------------------------
-- Semigroup and monoid properties of tries

checkSemigroupLeftPref :: Property
checkSemigroupLeftPref = forAll genTrie $ \t ->
    forAll (genPattern =<< genByteString) $ \p ->
        let t'  = Trie.insert p 1 t
            t'' = Trie.insert p 2 t
        in (t' <> t'') == t'

checkSemigroupAssoc :: Property
checkSemigroupAssoc = forAll (replicateM 3 genTrie) $ \[t1,t2,t3] ->
    (t1 <> t2) <> t3 == t1 <> (t2 <> t3)

checkMonoidId :: Property
checkMonoidId = forAll genTrie $ \t ->
    t <> mempty == t && mempty <> t == t

-------------------------------------------------------------------------------
-- Functor laws for tries

checkFunctorId :: Property
checkFunctorId = forAll genTrie $ \t ->
    fmap id t == id t

checkFunctorComp :: Property
checkFunctorComp = forAll genTrie $ \t ->
    fmap (f . g) t == (fmap f . fmap g) t
  where
    f, g :: Int -> Int
    f x = x + 1
    g x = x * 2

-------------------------------------------------------------------------------
-- Traversable laws for tries

checkTraversableId :: Property
checkTraversableId = forAll genTrie $ \t ->
    traverse Identity t == Identity t

checkTraversableComp :: Property
checkTraversableComp = forAll genTrie $ \t ->
    traverse (Compose . fmap g . f) t
    ==
    (Compose . fmap (traverse g) . traverse f) t
  where
    f, g :: Int -> Maybe Int
    f x = Just (x + 1)
    g x = Just (x * 2)

-------------------------------------------------------------------------------
-- Generators

genByteString :: Gen ByteString
genByteString = C8.pack <$> listOf1 arbitraryASCIIChar

-- Generate an input string matching a given pattern.
genStr :: Pattern ByteString -> Gen (Str ByteString)
genStr p = mapM gen (toList p)
  where
    gen  Trie.AnyStr   = genByteString
    gen (Trie.EqStr s) = pure s

genPattern :: ByteString -> Gen (Pattern ByteString)
genPattern prefix = do
    n <- choose (1, 10)
    s <- vectorOf n genMatcher
    return $ Seq.fromList (Trie.EqStr prefix : s)

-- Generate an arbitrary pattern together with a matching
-- input string.
genPatternWithStr :: Gen (Pattern ByteString, Str ByteString)
genPatternWithStr = do
    p <- genPattern ""
    s <- genStr p
    return (p, s)

genMatcher :: Gen (Matcher ByteString)
genMatcher = oneof [str, var]
  where
    str = Trie.EqStr <$> genByteString
    var = pure Trie.AnyStr

-- Generate 1-100 non-overlapping patterns
genPatterns :: Gen [(Pattern ByteString, Int)]
genPatterns = do
    n <- choose (1, 100)
    r <- mapM (genPattern . C8.pack . show) [1..n]
    return $ r `zip` [1..n]

genTrie :: Gen (Trie ByteString Int)
genTrie = Trie.fromAssocList <$> genPatterns

