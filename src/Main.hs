{-# LANGUAGE LambdaCase #-}

module Main (main) where

import           Calculator
import           Language
import           Parser

import           System.Environment
import           System.IO
import           System.Exit

import           Control.Applicative

main :: IO ()
main = do
  getArgs >>= \case
    [] -> error "No arguments. Expected file name with laws"
    [lawFileName] -> readFile lawFileName >>= parseLawsError >>= (interactive . go)
    _ -> error "Too many arguments. Expected one argument with file name containing laws"

parseLawsError :: String -> IO [Law VarName]
parseLawsError str =
  case parse (parseLaws <* many whitespace) str of
    Left err -> do
      putStrLn $ "Parse error in laws:\n" ++ err
      exitFailure
    Right r -> pure r

go :: [Law VarName] -> String -> IO ()
go laws proofStr =
  case parse (parseProofSteps laws <* many whitespace) proofStr of
    Left err -> putStrLn $ "Parse error in proof:\n" ++ err
    Right Nothing -> putStrLn $ "Cannot find law"
    Right (Just proofSteps) ->
      case verifyProofSteps proofSteps of
        Left err -> putStrLn $ "Error in proof:\n" ++ showCalcError err
        Right subst -> putStrLn "Correct."

interactive :: (String -> IO ()) -> IO ()
interactive f = do
  putStr "\\> "
  str <- getLines
  isEOF >>= \case
    True -> pure ()
    False -> do
      f str

getLines :: IO String
getLines = do
  str <- getLine
  if null str
    then return ""
    else fmap (str ++) getLines

