module Main


foo : IO ()
foo = putStrLn "foo"
























main : IO ()
main = do
    foo
    putStrLn "Hello world"
