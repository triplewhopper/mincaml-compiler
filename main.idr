module Main

import Binding
import Syntax
import Lexer
import Parser
import Utils
import Info
import Typing2
import KNormal
import Assoc 
import Beta
import NonNullString

import Data.SortedMap
import Data.String
import Data.List1
import Data.Maybe
import Text.Lexer
import System
import System.File
import System.Console.GetOpt
import System.File.Virtual

import Text.PrettyPrint.Prettyprinter.Render.String
import Text.PrettyPrint.Prettyprinter
import Text.PrettyPrint.Prettyprinter.Util


data Flag = LexOnly | ShowVerbose | ShowHelp | Output String | 
  Cmd String | S | ShowAst | ShowExtEnv | ShowKNormal | ShowANormal | ShowBeta | Input String
Eq Flag where 
  LexOnly == LexOnly = True
  ShowVerbose == ShowVerbose = True
  ShowHelp == ShowHelp = True
  Output a == Output b = a == b
  Cmd a == Cmd b = a == b
  S == S = True
  ShowAst == ShowAst = True
  ShowExtEnv == ShowExtEnv = True
  ShowKNormal == ShowKNormal = True
  ShowANormal == ShowANormal = True
  ShowBeta == ShowBeta = True
  Input a == Input b = a == b
  _ == _ = False
Show Flag where 
  show LexOnly = "LexOnly"
  show ShowVerbose = "ShowVerbose"
  show ShowHelp = "ShowHelp"
  show (Output a) = "Output " ++ a
  show (Cmd a) = "Cmd " ++ a
  show S = "S"
  show ShowAst = "ShowAst"
  show ShowExtEnv = "ShowExtEnv"
  show ShowKNormal = "ShowKNormal"
  show ShowANormal = "ShowANormal"
  show ShowBeta = "ShowBeta"
  show (Input a) = "Input " ++ a
options: List (OptDescr Flag)
options = [
  MkOpt ['l'] ["lex"] (NoArg LexOnly) "lex only",
  MkOpt ['v'] ["verbose"] (NoArg ShowVerbose) "show verbose",

  -- MkOpt ['c'] [] (ReqArg Cmd "cmd") "program passed in as string",
  MkOpt ['o'] [] (ReqArg Output "FILE") "output to FILE",
  -- MkOpt ['S'] [] (NoArg S) "Only run preprocess and compilation steps"
  MkOpt ['i'] ["iter"] (OptArg (Input . fromMaybe "3") "N") "number of iterations, default 3",
  MkOpt [] ["show-ast"] (NoArg ShowAst) "show ast node",
  MkOpt [] ["show-extenv"] (NoArg ShowExtEnv) "show extenv",
  MkOpt [] ["show-knormal"] (NoArg ShowKNormal) "show K-Normalized AST",
  MkOpt [] ["show-anormal"] (NoArg ShowANormal) "show A-normalized AST",
  MkOpt [] ["show-beta"] (NoArg ShowBeta) "show beta-reduced AST",
  MkOpt ['h'] ["help"] (NoArg ShowHelp) "show help message"
]
iter: (Info a) => Result Flag -> String -> Nat -> KNormal a -> IO (KNormal a)
iter res path Z kn = pure kn
iter res path (S n) kn = do 
  putStr $ "iter " ++ show n ++ "..."
  let (modified1, an) = Assoc.f kn
  let (modified2, bn) = Beta.f an
  if null modified1 && null modified2 then do 
    putStrLn "no change;"
    pure kn 
    else do 
    putStrLn "done."
    when (not (null modified2)) $ do 
      putStrLn $ "beta-reduced: " ++ show (length modified2) ++ " nodes"
      for_ modified2 $ \i => do 
        putStrLn $ show i.span
    when (ShowANormal `elem` res.options) $ do
      let s = show an
      Right () <- writeFile (path ++ ".a-norm#\{show n}.ml") s
        | Left err => die $ "Failed to write anormal to file \{show path}.a-norm.ml: " ++ show err
      pure ()
    when (ShowBeta `elem` res.options) $ do
      let s = show bn 
      Right () <- writeFile (path ++ ".beta#\{show n}.ml") s
        | Left err => die $ "Failed to write beta to file \{show path}.beta.ml: " ++ show err
      pure ()
    iter res path n bn

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
    putStrLn (usageInfo ("Usage: minmlc " ++ italics "file") options)

  when (not (null res.unrecognized)) $ do 
    let suffix = if (length res.unrecognized == 1) then "" else "s"
    die $ (bold . red) "error: " ++ bold ("unknown argument" ++ suffix ++ ": ") ++ (unwords . nub . (show <$>)) res.unrecognized

  when (ShowHelp `elem` res.options) $ do 
    exitSuccess

  case (res.nonOptions, res.errors) of 
    (self::[], errs) => do 
      die (concat errs ++ "\{self}: " ++ (bold . red) "error: " ++ bold "no input files")
    (_::n, []) => do
      for_ n $ \path => do
        when (not (isSuffixOf ".ml" path)) $ do 
          die $ "\{path}: " ++ (bold . red) "error: " ++ bold "file must have .ml extension"
        str <- fromFile path
        str <- 
          case str of 
            Left err => die "\{path}: \{show err}"
            Right (Left err) => die "\{path}: \{show err}"
            Right (Right str) => do
              when (LexOnly `elem` res.options) $ do 
                case (lexMinCaml str) of 
                  Left err => die $ "Unknown token:\nFile \{show path}, " ++ show err
                  Right toks => do 
                    Right () <- writeFile (path ++ ".tokens.txt") ("\n" `joinBy` (\x => "File \{show path}, " ++ show @{a3} x) <$> forget toks)
                      | Left err => die $ "Failed to write tokens to file \{show path}.tokens.txt: " ++ show err
                    pure ()
                exitSuccess
              pure str
        node <-
        case parse {path} str of 
          Left err => die $ "Unknown token:\nFile \{show path}, " ++ show err
          Right (Left err) => die $ show err
          Right (Right node) => pure node
        -- putStrLn $ "File \{show path}:\n" ++ show node
        (nodesTy, extEnv, ty) <- case infer' {path} node of 
          Left e => die e
          Right (nodesTy, extEnv, ty) => do 
            when (ShowExtEnv `elem` res.options) $ do
              Right () <- writeFile (path ++ ".extenv.txt") ("\n" `joinBy` (\(x, y) => show x ++ " : " ++ show y) <$> toList extEnv)
                | Left err => die $ "Failed to write extenv to file \{show path}.extenv.txt: " ++ show err
              pure ()
            putStrLn "(* ty: \{show ty} *)"
            when (ShowAst `elem` res.options) $ do
              let s = (renderString . layoutSmart ({ layoutPageWidth := AvailablePerLine (cast 80) 1 } defaultLayoutOptions)) $ the (Doc Bounds) $ pretty node
              Right () <- writeFile (path ++ ".ast.ml") s
                | Left err => die $ "Failed to write ast to file \{show path}.ast.ml: " ++ show err
              pure ()
            pure (nodesTy, extEnv, ty)
        (kn, knTy) <- case KNormal.f nodesTy node of 
          Left e => die "\{path}: \{e}"
          Right (kn, knTy) => do 
            when (ShowKNormal `elem` res.options) $ do
              let s = "(* ty: \{show knTy} *)\n" ++ show kn
              Right () <- writeFile (path ++ ".k-norm.ml") s
                | Left err => die $ "Failed to write knormal to file \{show path}.k-norm.ml: " ++ show err
              pure ()
            pure (kn, knTy)
        kn <- iter res path 3 kn
        pure ()
    (n, errs) => do 
      die (concat errs ++ usageInfo "Usage: minmlc FILE" options)

