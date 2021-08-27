module Parser where

import           Control.Monad

newtype ParseError = ParseError String

newtype Parser a = Parser (String -> Either ParseError (String, a))

instance Functor Parser where
  fmap f (Parser p) = Parser (fmap (fmap f) . p)

instance Applicative Parser where
  pure x = Parser (\str -> Right (str, x))
  (<*>) = ap

instance Monad Parser where
  (>>=) = undefined

parseError :: String -> Either ParseError a
parseError = Left . ParseError

parse :: Parser a -> String -> Either ParseError a
parse (Parser p) str =
  case p str of
    Left err -> Left err
    Right ("", r) -> Right r
    Right (_, _) -> parseError "Incomplete parse"

char :: Char -> Parser Char
char c = Parser $ \str ->
  case str of
    [] -> parseError $ "End of input. Expected " <> show c
    (c':rest) ->
      if c' == c
        then Right (rest, c)
        else parseError $ "Could not match " <> show c' <> " with " <> show c

-- string :: String -> Parser String
-- string str0 = mapM char str0

