module Main


foo : IO ()
foo = putStrLn "foo"










data Foo = Foo1 | Foo2
data Bar = Bar1 | Bar2


barify : Foo -> Bar
barify Foo1 = Bar1
barify Foo2 = Bar1















main : IO ()
main = do
    foo
    putStrLn "Hello world"
