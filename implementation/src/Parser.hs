{-# OPTIONS_GHC -fno-warn-missing-signatures #-}

module Parser (parseString) where

import Text.Parsec
import Text.Parsec.Expr
import Text.Parsec.Language
import Text.Parsec.String
import qualified Text.Parsec.Token as Token

import Syntax

-- Lexing

reservedOpNames = [ "+", "<=", "=", "\\", ":", ".", "<" , "->", "[]" ]

reservedNames   = [ "true", "false", "if", "then", "else", "let", "in"
                  , "fst", "snd", "with", "length", "loop", "for", "do"
                  , "int", "bool"
                  ]

lexerConfig = emptyDef { Token.reservedOpNames = reservedOpNames
                       , Token.reservedNames   = reservedNames
                       , Token.identStart      = letter
                       , Token.identLetter     = alphaNum <|> char '\''
                       }

lexer = Token.makeTokenParser lexerConfig

reserved   = Token.reserved   lexer
reservedOp = Token.reservedOp lexer
integer    = Token.integer    lexer
whitespace = Token.whiteSpace lexer
identifier = Token.identifier lexer
parens     = Token.parens     lexer
commaSep   = Token.commaSep   lexer
brackets   = Token.brackets   lexer
colon      = Token.colon      lexer
dot        = Token.dot        lexer
comma      = Token.comma      lexer

-- Parsing

infixOp s f assoc = Infix (f <$ reservedOp s) assoc

notReservedOp = notFollowedBy . choice
                  . map reservedOp $ Token.reservedOpNames lexerConfig

opTable = [ [ Infix (whitespace *> notReservedOp *> return App) AssocLeft ]
          , [ infixOp "+"  Add AssocLeft ]
          , [ infixOp "<=" LEq AssocNone ]
          ]

parseString :: String -> Either ParseError Expr
parseString = parse (parseExpr <* eof) ""

parseExpr :: Parser Expr
parseExpr = buildExpressionParser opTable parseExpr1

parseExpr1 :: Parser Expr
parseExpr1 =  parseBool
          <|> parseIf
          <|> parseLambda
          <|> parseLet
          <|> parseProj
          <|> parseArray
          <|> parseLength
          <|> parseLoop
          <|> Num . fromIntegral <$> integer
          <|> Var <$> identifier
          <|> parseParens

parseBool :: Parser Expr
parseBool =  TrueLit  <$ reserved "true"
         <|> FalseLit <$ reserved "false"

parseIf :: Parser Expr
parseIf = If <$> (reserved "if"   *> parseExpr)
             <*> (reserved "then" *> parseExpr)
             <*> (reserved "else" *> parseExpr)

parseLambda :: Parser Expr
parseLambda = do reservedOp "\\"
                 x  <- identifier <* colon
                 tp <- parseType  <* dot
                 e  <- parseExpr
                 return $ Lam x tp e

parseLet :: Parser Expr
parseLet = do reserved "let"
              x <- identifier
              reservedOp "="
              e1 <- parseExpr
              reserved "in"
              e2 <- parseExpr
              return $ Let x e1 e2

parseParens :: Parser Expr
parseParens = do es <- parens $ parseExpr `sepBy` comma
                 case es of
                   [e1, e2] -> return $ Pair e1 e2
                   [e]      -> return e
                   _        -> fail "only binary products for now"

parseProj :: Parser Expr
parseProj =  Fst <$> (reserved "fst" *> parseExpr)
         <|> Snd <$> (reserved "snd" *> parseExpr)

parseArray :: Parser Expr
parseArray = ArrayLit <$> brackets (commaSep parseExpr)

parseLength :: Parser Expr
parseLength = Length <$> (reserved "length" *> parseExpr)

parseLoop :: Parser Expr
parseLoop = do reserved "loop"
               x <- identifier
               reservedOp "="
               e1 <- parseExpr
               reserved "for"
               y <- identifier
               reservedOp "<"
               e2 <- parseExpr
               reserved "do"
               e3 <- parseExpr
               return $ Loop x e1 y e2 e3

parseType :: Parser Tp
parseType = aux `chainr1` (TpArrow <$ reservedOp "->")
  where aux =  TpInt   <$  reserved "int"
           <|> TpBool  <$  reserved "bool"
           <|> TpArray <$> (reservedOp "[]" *> aux)
           <|> parens (do t1 <- parseType
                          (TpPair t1 <$> (try comma *> parseType)) <|> return t1)
