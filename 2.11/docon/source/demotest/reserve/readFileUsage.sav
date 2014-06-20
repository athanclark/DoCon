
main = readFile "foo.txt" >>= putStr

       -- or    do contents <- readFile "foo.txt"
       --       putStr contents

-- Note: `readFile` reads lazily, which means that strangeness can 
-- result if the file is written simultaneously with your program's 
-- execution.
