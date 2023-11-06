module Main

import Data.SortedMap
import Ty
-- import Typing
import Data.String
import Data.List1
import Text.Lexer
import System
import System.File
import System.Console.GetOpt
import System.File.Virtual
import Syntax
import Lexer
import Parser
import Utils

data Flag = LexOnly | ShowVerbose | ShowHelp | Output String | Cmd String | S
Eq Flag where 
    LexOnly == LexOnly = True
    ShowVerbose == ShowVerbose = True
    ShowHelp == ShowHelp = True
    Output a == Output b = a == b
    Cmd a == Cmd b = a == b
    S == S = True
    _ == _ = False
Show Flag where 
    show LexOnly = "LexOnly"
    show ShowVerbose = "ShowVerbose"
    show ShowHelp = "ShowHelp"
    show (Output a) = "Output " ++ a
    show (Cmd a) = "Cmd " ++ a
    show S = "S"
options: List (OptDescr Flag)
options = [
    MkOpt ['l'] ["lex"] (NoArg LexOnly) "lex only",
    MkOpt ['v'] ["verbose"] (NoArg ShowVerbose) "show verbose",

    -- MkOpt ['c'] [] (ReqArg Cmd "cmd") "program passed in as string",
    MkOpt ['o'] [] (ReqArg Output "FILE") "output to FILE",
    -- MkOpt ['S'] [] (NoArg S) "Only run preprocess and compilation steps"
    MkOpt ['h'] ["help"] (NoArg ShowHelp) "show help message"
]

red: String -> String
red str = "\x1b[91m\{str}\x1b[0m"
bold: String -> String
bold str = "\x1b[1m\{str}\x1b[0m"
italian: String -> String
italian str = "\x1b[3m\{str}\x1b[0m"

main: IO ()
main = do 
  args <- getArgs
  let res = getOpt Permute options args
  when (ShowVerbose `elem` res.options) $ do 
    putStrLn "options: \{show res.options}"
    putStrLn "non-options: \{show res.nonOptions}"
    putStrLn "unrecognized options: \{show res.unrecognized}"
    putStrLn "errors: \{show res.errors}"

  when (ShowHelp `elem` res.options) $ do 
    putStrLn (usageInfo ("Usage: minmlc " ++ italian "file") options)

  when (not (null res.unrecognized)) $ do 
    let suffix = if (length res.unrecognized == 1) then "" else "s"
    die $ (bold . red) "error: " ++ bold ("unknown argument" ++ suffix ++ ": ") ++ (unwords . nub . (show <$>)) res.unrecognized

  when (ShowHelp `elem` res.options) $ do 
    exitSuccess

  case (res.nonOptions, res.errors) of 
    (self::[], errs) => do 
        die (concat errs ++ "\{self}: " ++ (bold . red) "error: " ++ bold "no input files")
    (_::n, []) => do
        if LexOnly `elem` res.options then 
            for_ n $ \path => do
                str <- fromFile path
                case str of 
                    Left err => die "\{path}: \{show err}"
                    Right (Left err) => die "\{path}: \{show err}"
                    Right (Right str) =>
                        case (lexMinCaml str) of 
                            Left err => die $ "Unknown token:\nFile \{show path}, " ++ show err
                            Right toks => putStrLn $  "\n" `joinBy` (\x => "File \{show path}, " ++ show @{a3} x) <$> forget toks
          else for_ n $ \path => do
            str <- fromFile path
            case str of 
                Left err => die "\{path}: \{show err}"
                Right (Left err) => die "\{path}: \{show err}"
                Right (Right str) =>
                    case parse {path} str of 
                        Left err => die $ "Unknown token:\nFile \{show path}, " ++ show err
                        Right (Left err) => die $ "\n" `joinBy` show <$> forget err
                        Right (Right node) => putStrLn $ show node
    (n, errs) => do 
      die (concat errs ++ usageInfo "Usage: minmlc FILE" options)

