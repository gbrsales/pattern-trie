{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Control.DeepSeq
import Criterion.Main
import Data.ByteString (ByteString)
import Data.Foldable
import Data.Hashable
import Data.Sequence (Seq)
import Data.Text (Text)
import Data.Text.Encoding (decodeUtf8)
import Data.Trie.Pattern

import qualified Data.Sequence as Seq
#if __GLASGOW_HASKELL__ < 804
import qualified Data.Trie     as BST
#endif

main :: IO ()
main = defaultMain
    [ bgroup "pattern-trie (ByteString)"
        [ env (genStaticPTrie staticBKeys) $
            bench "match (static)" . ptrieBMatch
        , env (genPTrie captureBKeys) $
            bench "match (capture)" . ptrieBMatch
        ]
    , bgroup "pattern-trie (Text)"
        [ env (genStaticPTrie staticTKeys) $
            bench "match (static)" . ptrieTMatch
        , env (genPTrie captureTKeys) $
            bench "match (capture)" . ptrieTMatch
        ]
#if __GLASGOW_HASKELL__ < 804
    , bgroup "bytestring-trie"
        [ env (genBSTrie staticBKeys) $
            bench "lookup" . bstrieLookup
        ]
#endif
    ]

------------------------------------------------------------------------------
-- pattern-trie

-- Generators

genStaticPTrie :: (Eq s, Hashable s) => [Str s] -> IO (Trie s Int)
genStaticPTrie keys = genPTrie (map mkPat keys)
  where
    mkPat = Seq.fromList . map EqStr

genPTrie :: (Eq s, Hashable s) => [Pattern s] -> IO (Trie s Int)
genPTrie pats = return $! build pats
  where
    build = fromAssocList . (`zip` [1..])

-- Benchmarks

ptrieBMatch :: Trie ByteString Int -> Benchmarkable
ptrieBMatch t = nf run bchunks
  where
    run :: Str ByteString -> Maybe (Int, Seq (Capture ByteString))
    run s = match s t

ptrieTMatch :: Trie Text Int -> Benchmarkable
ptrieTMatch t = nf run tchunks
  where
    run :: Str Text -> Maybe (Int, Seq (Capture Text))
    run s = match s t

------------------------------------------------------------------------------
-- bytestring-trie

#if __GLASGOW_HASKELL__ < 804

-- Generators

newtype BSTrie a = BSTrie (BST.Trie a)

instance NFData (BSTrie a) where
    rnf t = t `seq` ()

genBSTrie :: [[ByteString]] -> IO (BSTrie Int)
genBSTrie keys = return $! build keys
  where
    build = BSTrie . BST.fromList . (`zip` [1..]) . map mconcat

-- Benchmarks

bstrieLookup :: BSTrie Int -> Benchmarkable
bstrieLookup (BSTrie t) = nf run (mconcat bchunks)
  where
    run :: ByteString -> Maybe Int
    run s = BST.lookup s t

#endif

------------------------------------------------------------------------------
-- Test keys

staticBKeys :: [[ByteString]]
staticBKeys = genKeys bchunks

staticTKeys :: [[Text]]
staticTKeys = genKeys tchunks

captureBKeys :: [Pattern ByteString]
captureBKeys = captureKeys bchunks

captureTKeys :: [Pattern Text]
captureTKeys = captureKeys tchunks

captureKeys :: [s] -> [Pattern s]
captureKeys chunks = map Seq.fromList (genKeys matchers)
  where
    -- Replace the last chunk with a "capture", so it can appear at every
    -- position of a generated key.
    matchers = map EqStr (init chunks) ++ [AnyStr]

-- Given a list of length n, generate n! lists (i.e. keys), each of length n,
-- whereby the i'th item in the input list appears at positions 1..i. E.g. the
-- 1st item only appears as the 1st chunk of a path, the 2nd item can appear as
-- the 1st and 2nd chunk of a path, ..., the nth item can appear at any position
-- of a path (and in particular, it is the last chunk of every path).
--
-- For example:
-- @
-- genKeys [1..3]
-- [[1,2,3],[1,3,3],[2,2,3],[2,3,3],[3,2,3],[3,3,3]]
-- @
genKeys :: [a] -> [[a]]
genKeys l = mapM next [0..(length l - 1)]
  where
    next i = drop i l

-- (Static) ByteString chunks from which the keys of the tries are built up.
bchunks :: [ByteString]
bchunks =
    [ "abcde"
    , "bcdef"
    , "cdefg"
    , "defgh"
    , "efghi"
    , "fghij"
    ]

tchunks :: [Text]
tchunks = map decodeUtf8 bchunks

