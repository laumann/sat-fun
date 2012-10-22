{-
  This is an implementation of the FUN language as presented in the 
  DIKU course 'Semantics and Types' (SaT).
-}
module FUN where

import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Language (haskellStyle)

lambda = "λ"
leq    = "≤"

-- Reserved words in FUN
reserved_words = ["true", "false", "if", "then", "else", "fst", 
                  "snd", lambda, "let", "in", "rec" ]

type Id = String

-- | Grammar of FUN
data Term = TNum Integer
          | TBool Bool
          | TVar Id
          | TPlus Term Term
          | TLeq Term Term
          | TIf Term Term Term
          | TPair Term Term
          | TFst Term
          | TSnd Term
          | TLam Id Term
          | TApp Term Term
          | TLet Id Term Term
          | TRec Id Term
          deriving Show

type Program = [Term]

testprog = "rec f.λx.λy if 0 =< x then y else f (x+1) y"

nesting :: Parser Int
nesting = do char '('
             n <- nesting
             char ')'
             m <- nesting
             return $ max (n+1) m
          <|> return 0

--num = token $ do str <- many1 digit
  --               return $ read str


program :: Parser Program
program = many1 term


term :: Parser Term
term = tNum <|> tBool <|> tVar <|> tIf

tNum = do spaces 
          n <- num
          return $ TNum n

tBool = do spaces
           t <- (symbol "true" <|> symbol "false")
           return $ TBool $ t == "true"

tVar = do v <- var
          return $ TVar v

tPlus = undefined

tLeq = undefined

tIf = do keyword "if"
         t0 <- term
         keyword "then"
         t1 <- term
         keyword "else"
         t2 <- term
         return $ TIf t0 t1 t2

tPair = undefined

tFst = undefined

tSnd = undefined

tLam = undefined

tApp = undefined

tLet = undefined

tRec = undefined

num :: Parser Integer
num = do s <- many1 digit
         return $ read s

var :: Parser Id
var = do spaces
         v <- letter
         vs <- many (letter <|> digit)
         return $ v:vs
         

keyword :: String -> Parser ()         
keyword s = spaces >> (try $ string s) >> return ()

symbol :: String -> Parser String
symbol s = try $ string s >>= \s -> return s
              

run :: (Show a) => Parser a -> String -> IO ()
run p input = case (parse p "" input) of
  Right x  -> print x
  Left err -> do putStr "parse error at "
                 print err

runEof :: Parser a -> String -> IO ()
runEof p = run (p >> eof)