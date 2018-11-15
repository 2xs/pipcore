#!/usr/bin/runhaskell
---------------------------------------------------------------------------------
--  © Université Lille 1, The Pip Development Team (2015-2018)                 --
--                                                                             --
--  This software is a computer program whose purpose is to run a minimal,     --
--  hypervisor relying on proven properties such as memory isolation.          --
--                                                                             --
--  This software is governed by the CeCILL license under French law and       --
--  abiding by the rules of distribution of free software.  You can  use,      --
--  modify and/ or redistribute the software under the terms of the CeCILL     --
--  license as circulated by CEA, CNRS and INRIA at the following URL          --
--  "http://www.cecill.info".                                                  --
--                                                                             --
--  As a counterpart to the access to the source code and  rights to copy,     --
--  modify and redistribute granted by the license, users are provided only    --
--  with a limited warranty  and the software's author,  the holder of the     --
--  economic rights,  and the successive licensors  have only  limited         --
--  liability.                                                                 --
--                                                                             --
--  In this respect, the user's attention is drawn to the risks associated     --
--  with loading,  using,  modifying and/or developing or reproducing the      --
--  software by the user in light of its specific status of free software,     --
--  that may mean  that it is complicated to manipulate,  and  that  also      --
--  therefore means  that it is reserved for developers  and  experienced      --
--  professionals having in-depth computer knowledge. Users are therefore      --
--  encouraged to load and test the software's suitability as regards their    --
--  requirements in conditions enabling the security of their systems and/or   --
--  data to be ensured and,  more generally, to use and operate it in the      --
--  same conditions as regards security.                                       --
--                                                                             --
--  The fact that you are presently reading this means that you have had       --
--  knowledge of the CeCILL license and that you accept its terms.             --
---------------------------------------------------------------------------------

-- Indenter for Pip Coq source code
--
-- Warning: This is _just_ a heuristic, it makes some assumptions on
-- the initial layout, namely:
--
--  - if-then-else's are written either with "then" and "else" each
--    starting on a fresh line, or both of them on one line with words
--    before (such as the "if")
--  - "match" and "end" both appear at the beginning of a line
--  - comments can be nested but detection of opening and closing is
--    easily fooled
--  - the period ending a sentence "." is at the end of the line
--    (in particular, a comment after the period breaks its detection)

import Data.List
import Data.Char
import Control.Monad.State

data Tag = Match | If | Comment
    deriving Show
type IndentLevel = Int
data IndenterState = S { curIndentLevel :: IndentLevel
                       , indentStack    :: [ (Tag, IndentLevel) ] }
                       deriving Show
type IndenterMonad = State IndenterState

initState = S 0 []

inComment :: IndenterMonad Bool
inComment = do s <- get
               return $ case indentStack s of
                          (Comment, _) : _ -> True
                          _                -> False

trim :: String -> String
trim = dropWhileEnd isSpace . dropWhile isSpace

ins :: IndentLevel -> String -> String
ins _  "" = ""
ins l str = replicate (l * 2) ' ' ++ str

insM :: IndentLevel -> String -> IndenterMonad String
insM l str = do comment <- inComment
                when (not comment && "." `isSuffixOf` str) (put initState)
                return $ ins l str

insCurM :: String -> IndenterMonad String
insCurM str = get >>= \s -> insM (curIndentLevel s) str

indent :: String -> IndenterMonad String
indent str | "Definition" `isPrefixOf` str = reset 1 str
           | "Fixpoint"   `isPrefixOf` str = reset 1 str
           | "then"       `isPrefixOf` str = ucai If 1 str
           | "else"       `isPrefixOf` str = do S _ ((If, l) : is) <- get
                                                put (S (l+1) is)
                                                insM l str
           | "match"      `isPrefixOf` str = ucai Match 0 str
           | "|"          `isPrefixOf` str = do S _ is@((Match, l) : _) <- get
                                                put (S (l+1) is)
                                                insM l str
           | "end"        `isPrefixOf` str = do S _ ((Match, l) : is) <- get
                                                put (S l is)
                                                insM l str

           | "(*" `isPrefixOf` str && not ("*)" `isInfixOf` str) = ucai Comment 1 str
           | "*)" `isSuffixOf` str && not ("(*" `isInfixOf` str) = do S l ((Comment, l') : is) <- get
                                                                      put (S l' is)
                                                                      insM l str

           | otherwise                     = insCurM str

    where -- | Use Current And Indent
          ucai :: Tag -> IndentLevel -> String -> IndenterMonad String
          ucai tag l str = do s <- get
                              put (S (curIndentLevel s + l)
                                     ((tag, curIndentLevel s) : indentStack s))
                              insM (curIndentLevel s) str

          -- | Reset state, when not in comment
          reset :: IndentLevel -> String -> IndenterMonad String
          reset l str = do comment <- inComment
                           s <- get
                           if comment
                               then do put (S (curIndentLevel s + l) (indentStack s))
                                       insM (curIndentLevel s) str
                               else do S _ [] <- get -- just to check
                                       put (S l [])
                                       insM (l-1) str

indentAll :: [ String ] -> [ String ]
indentAll strs = evalState (mapM indent strs) initState

main = interact (unlines . indentAll . map trim . lines)
