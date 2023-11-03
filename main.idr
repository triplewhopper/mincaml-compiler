module Main

import Control.App
import Control.App.Console
import Control.App.FileIO
import Data.SortedMap
import Ty
import Typing
import System.File.Virtual
import Syntax

hello: Console es => App es ()
hello = do
    putStrLn "Hello, App World!"

data S1: Type where 

data S2: Type where 

data S3: Type where

fuck: Has [Exception UnifyErr, Exception IOError, State S1 Nat, Console, State S2 Nat, State S3 Nat] e => Nat -> App e Nat
fuck n = do 
    modify S1 (+(n+1))
    modify S2 (+(n+7))
    -- throw (GenericErr "fuck you")
    modify S3 (+(n+10))
    pure 6

new3: t1 -> t2 -> t3 -> (Has [State tag1 t1, State tag2 t2, State tag3 t3] e => App e a) -> App e a
new3 val1 val2 val3 prog = new val1 (new val2 (new val3 prog))

-- extEnvManager: Node -> Has [Exception UnifyErr, EConsole, UnionFindI, TyVarGenI, ExtEnvI] e => App e ()
-- extEnvManager node = 
--     handle (handle (infer {env=[]} node) (\typ => putStrLn $ show typ ++ show !(get ())) (\err: IOError => putStrLn $ show err))
--     (\p => pure ()) (\err: UnifyErr => putStrLn $ "Error: \{show err}")

mainApp: Node -> App Init ()
mainApp node =
    handle (
        handle (new3 UnionFind.empty (the Nat 0) [] (infer {env=[]} node)) 
        (\typ => putStrLn $ "\{show typ}")
        (\err: IOError => putStrLn $ show err)
    ) (\p => pure ()) (\err: UnifyErr => putStrLn $ "Error: \{show err}")
    


-- mainApp = handle (handle (new3 0 0 0 (fuck 2)) (\str => putStrLn $ "kkk" ++ show str)(\err: UnifyErr => putStrLn $ show err)
--     ) (\str => putStrLn $ "jjj" ++ show str) (\err: IOError => putStrLn $ show err)

main: IO ()
main = run $ mainApp (Add (I 1 {key=0}) (B True {key=0}) {key=0})

