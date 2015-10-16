import Text.Parsec
import Text.Parsec.String
import System.Console.Haskeline

import Data.Set(empty)

import Eddie

data Command = Fact String Sentence
             | Prove Sentence
             | Ask Name Sentence
             | Clear
             | Help
             | Quit
               deriving (Show)

parseCommand :: Parser Command
parseCommand = do
    (try
        (do
            spaces
            string "Fact"
            spaces
            s <- parseSentence
            spaces
            n <- (option "Given." (do string "{"
                                      spaces
                                      x <- many1 $ noneOf "}"
                                      spaces
                                      string "}"
                                      return x))
            spaces
            eof
            return $ Fact n s))
    <|>
    (try
        (do
            spaces
            string "Prove"
            spaces
            s <- parseSentence
            spaces
            eof
            return $ Prove s))
    <|>
    (try
        (do
            spaces
            string "Clear"
            spaces
            eof
            return $ Clear))
    <|>
    (try
        (do
            spaces
            string "Help"
            spaces
            eof
            return $ Help))
    <|>
    (try
        (do
            spaces
            string "Quit"
            spaces
            eof
            return $ Quit))
    <|>
    (try
        (do
            spaces
            string "Ask"
            spaces
            r <- parseName
            spaces
            s <- parseSentence
            spaces
            eof
            return $ Ask r s))

parseSentence :: Parser Sentence
parseSentence = do
    a <- (try parseForall) <|> (try parseExists) <|> parseIff
    return a

parseForall :: Parser Sentence
parseForall = do
    string "Forall"
    spaces
    a <- parseName
    spaces
    b <- parseSentence
    return $ Forall a b

parseExists :: Parser Sentence
parseExists = do
    string "Exists"
    spaces
    a <- parseName
    spaces
    b <- parseSentence
    return $ Exists a b

parseIff :: Parser Sentence
parseIff = try (do
    l <- parseImplies
    spaces
    string "<=>"
    spaces
    r <- parseIff
    return $ Iff l r) <|> parseImplies

parseImplies :: Parser Sentence
parseImplies = try (do
    l <- parseAnd
    spaces
    string "=>"
    spaces
    r <- parseImplies
    return $ Implies l r) <|> parseAnd

parseAnd :: Parser Sentence
parseAnd = try (do
    l <- parseOr
    spaces
    string "&&"
    spaces
    r <- parseAnd
    return $ And l r) <|> parseOr

parseOr :: Parser Sentence
parseOr = try (do
    l <- parseNot
    spaces
    string "||"
    spaces
    r <- parseOr
    return $ Or l r) <|> parseNot

parseNot :: Parser Sentence
parseNot = try (do
    string "!"
    spaces
    p <- parsePredicate
    return $ Not p) <|> parseEquality

parseEquality :: Parser Sentence
parseEquality = try (do
    l <- parseTerm
    spaces
    string "=="
    spaces
    r <- parseTerm
    return $ Pred (Predicate (Name "Eq") [l, r])) <|> parsePredicate

parsePredicate :: Parser Sentence
parsePredicate = (try
    (do
        string "("
        spaces
        x <- parseSentence
        spaces
        string ")"
        return x)
    ) <|>
    (do
        x <- parseName
        y <- option []
            (do
                string "["
                r <- sepBy parseTerm (spaces *> string "," *> spaces)
                string "]"
                return r)
        return (Pred (Predicate x y)))

parseTerm :: Parser Term
parseTerm = (try parseFunction) <|> parseVariable

parseFunction :: Parser Term
parseFunction = do
    x <- parseName
    y <- (do
            string "("
            r <- sepBy parseTerm (spaces *> string "," *> spaces)
            string ")"
            return r)
    return (Function x y)

parseVariable :: Parser Term
parseVariable = do
    v <- parseName
    return (Variable v)

parseName :: Parser Name
parseName = do
    x <- many1 alphaNum
    return (Name x)


runRepl :: [Clause] -> InputT IO ()
runRepl kb = do
    minput <- getInputLine ("[" ++ (show $ length kb) ++"] ")
    case minput of
      Nothing       -> (do outputStrLn "So long, and thanks for all the fish!"; return ())
      Just ""       -> runRepl kb
      Just ('#':_)  -> runRepl kb
      Just input    -> (case parse parseCommand "parser" input of
                        (Left _) -> (do outputStrLn "Parse error: type `Help` for help.";
                                        runRepl kb)
                        (Right (Clear)) -> runRepl []
                        (Right (Fact n f)) -> (do outputStrLn "Sure thing, fella.";
                                                  runRepl ((sentenceToClauses n $ simplify $ f)++kb))
                        (Right (Prove f)) -> (do outputStrLn $ show ((sentenceToClauses "Negate goal" $ simplify $ (Not f))++kb)
                                                 outputStrLn
                                                    $ displayProof
                                                        (prove'
                                                            kb
                                                            ((sentenceToClauses
                                                              "Negate goal" $ simplify $ (Not f))));
                                                 runRepl kb)
                        (Right (Ask n st)) -> (do outputStrLn
                                                     $ (case (ask (kb ++ (sentenceToClauses "Negate goal" $ simplify $ (Or (Not st) (Pred (Predicate (Name "Answer") [Variable n])))))) of
                                                        Nothing -> "INSUFFICIENT DATA FOR MEANINGFUL ANSWER."
                                                        Just (t, c) -> displayProof c)
                                                  runRepl kb)
                        (Right (Help)) -> (do outputStrLn "Read the docs.";
                                              runRepl kb)
                        (Right (Quit)) -> (do outputStrLn "So long, and thanks for all the fish!";
                                              return ()))

main = do
    putStrLn "   +------------------------+\n\
             \   | Hi, I'm Eddie.         |\n\
             \   | I am a theorem prover. |\n\
             \   +------------------------+"
    runInputT defaultSettings (runRepl [])
    return ()
