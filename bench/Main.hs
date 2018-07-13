{-# LANGUAGE CPP #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import Control.DeepSeq
import Criterion.Main
import Data.ByteString (ByteString)
import Data.Foldable
import Data.Sequence (Seq)
import Data.Trie.Pattern

import qualified Data.Sequence as Seq
#if __GLASGOW_HASKELL__ < 804
import qualified Data.Trie     as BST
#endif

main :: IO ()
main = defaultMain
    [ bgroup "pattern-trie"
        [ env (genStaticPTrie staticKeys) $
            bench "match (static)" . ptrieMatch
        , env (genPTrie captureKeys) $
            bench "match (capture)" . ptrieMatch
        ]
#if __GLASGOW_HASKELL__ < 804
    , bgroup "bytestring-trie"
        [ env (genBSTrie staticKeys) $
            bench "lookup" . bstrieLookup
        ]
#endif
    ]

------------------------------------------------------------------------------
-- pattern-trie

genStaticPTrie :: [[ByteString]] -> IO (Trie Int)
genStaticPTrie keys = genPTrie (map mkPat keys)
  where
    mkPat = Seq.fromList . map EqStr

genPTrie :: [Pattern] -> IO (Trie Int)
genPTrie pats = return $! build pats
  where
    build = fromAssocList . (`zip` [1..])

ptrieMatch :: Trie Int -> Benchmarkable
ptrieMatch t = nf run chunks
  where
    run :: Str -> Maybe (Int, Seq Capture)
    run s = match s t

------------------------------------------------------------------------------
-- bytestring-trie

#if __GLASGOW_HASKELL__ < 804

newtype BSTrie a = BSTrie (BST.Trie a)

instance NFData (BSTrie a) where
    rnf t = t `seq` ()

genBSTrie :: [[ByteString]] -> IO (BSTrie Int)
genBSTrie keys = return $! build keys
  where
    build = BSTrie . BST.fromList . (`zip` [1..]) . map mconcat

bstrieLookup :: BSTrie Int -> Benchmarkable
bstrieLookup (BSTrie t) = nf run (mconcat chunks)
  where
    run :: ByteString -> Maybe Int
    run s = BST.lookup s t

#endif

------------------------------------------------------------------------------
-- Test keys

staticKeys :: [[ByteString]]
staticKeys = genKeys chunks

captureKeys :: [Pattern]
captureKeys = map Seq.fromList (genKeys matchers)
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

-- (Static) chunks from which the keys of the tries are built up.
chunks :: [ByteString]
chunks =
    [ "abcde"
    , "bcdef"
    , "cdefg"
    , "defgh"
    , "efghi"
    , "fghij"
    ]

