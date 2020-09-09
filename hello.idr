module Main


foo : IO ()
foo = putStrLn "foo"










data Foo = Foo1 | Foo2
data Bar = Bar1 | Bar2


barify : Foo -> Bar















main : IO ()
main = do
    foo
    putStrLn "Hello world"
