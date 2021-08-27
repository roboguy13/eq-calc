module Parser where

import           Control.Monad
import           Control.Applicative
import           Data.List

data ParseError = ParseError Pos String
  -- deriving (Show)

data Pos = Pos Int Int

initialPos :: Pos
initialPos = Pos 1 1

showPos :: Pos -> String
showPos (Pos line col) = "line " <> show line <> ", column " <> show col

nextPos :: Pos -> Char -> Pos
nextPos (Pos line col) c =
  if c `elem` "\n\r"
    then Pos (line+1) 1
    else Pos line (col+1)

nextPosStr :: Pos -> String -> Pos
nextPosStr pos str = foldl' nextPos pos str

newtype Parser a = Parser { runParser :: (String, Pos) -> Either ParseError ((String, Pos), a) }

updateError :: (Pos -> String -> ParseError) -> Parser a -> Parser a
updateError f (Parser p) =
  Parser $ \arg@(str, pos) ->
    case p arg of
      Left _ -> Left (f pos str)
      r -> r

couldn'tMatch :: (Show a, Show b) => Pos -> a -> b -> ParseError
couldn'tMatch pos x = couldn'tMatchMsg pos (show x)

couldn'tMatchMsg :: Show a => Pos -> String -> a -> ParseError
couldn'tMatchMsg pos msg x = ParseError pos $ "Expected " <> msg <> ". Found " <> show x

instance Functor Parser where
  fmap f (Parser p) = Parser (fmap (fmap f) . p)

instance Applicative Parser where
  pure x = Parser (\arg -> Right (arg, x))
  (<*>) = ap

instance Monad Parser where
  Parser p >>= f = Parser $ \str ->
    case p str of
      Left err        -> Left err
      Right (rest, x) -> runParser (f x) rest

instance Alternative Parser where
  empty = Parser (\(_, pos) -> (parseError pos "Empty parser"))
  Parser p <|> Parser q = Parser (p <> q)

parseError :: Pos -> String -> Either ParseError a
parseError pos = Left . ParseError pos

showParseError :: ParseError -> String
showParseError (ParseError pos err) =
  "At " <> showPos pos <> ":"
  <> "\n" <> err

parse :: Parser a -> String -> Either String a
parse (Parser p) str =
  case p (str, initialPos) of
    Left err -> Left (showParseError err)
    Right (("", _), r) -> Right r
    Right ((rest, pos), _) -> Left $ "Incomplete parse. Leftover: " <> show rest

acceptCharWhen :: (Char -> Bool) -> Parser Char
acceptCharWhen predicate = Parser $ \(str, pos) ->
  case str of
    [] -> parseError pos "acceptCharWhen: []"
    (c:rest)
      | predicate c -> Right ((rest, nextPos pos c), c)
      | otherwise   -> parseError pos $ "acceptCharWhen: Got " <> show c

oneOf :: [Char] -> Parser Char
oneOf cs =
  updateError (\pos c -> ParseError pos $ "Found " <> show c <> ". Expected one of " <> intercalate ", " (map show cs))
    $ acceptCharWhen (`elem` cs)

char :: Char -> Parser Char
char c = updateError (\pos -> couldn'tMatch pos c) $ oneOf [c]

string :: String -> Parser String
string str0 = updateError (\pos -> couldn'tMatch pos str0) $ mapM char str0

whitespace :: Parser Char
whitespace = oneOf " \t\n\r"

alpha :: Parser Char
alpha = updateError (\pos -> couldn'tMatchMsg pos "alphabetical character") $ oneOf (['a'..'z'] ++ ['A'..'Z'])

digit :: Parser Char
digit = updateError (\pos -> couldn'tMatchMsg pos "digit") $ oneOf ['0'..'9']

alphanum :: Parser Char
alphanum = updateError (\pos -> couldn'tMatchMsg pos "alphanumerical character") (alpha <|> digit)

operatorSymbol :: Parser Char
operatorSymbol = updateError (\pos -> couldn'tMatchMsg pos "operator symbol") $ acceptCharWhen cond
  where
    cond c = not (c `elem` (['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ " \t\n\r" ++ "{}"))

operator :: Parser String
operator = some operatorSymbol

bracketed :: Parser a -> Parser a -> Parser b -> Parser b
bracketed start end p = do
  start
  r <- p
  end
  return r

parens :: Parser a -> Parser a
parens = bracketed (char '(') (char ')')

