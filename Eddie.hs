{-
References:
- http://www.ki.informatik.uni-frankfurt.de/persons/panitz/paper/russian.ps
- http://src.seereason.com/chiou-prover/report.ps
- http://www.cs.nott.ac.uk/~led/papers/led_bsc_dissertation.pdf
- http://www.cs.toronto.edu/~sheila/384/w11/Lectures/csc384w11-KR-tutorial.pdf

- http://www.mathcs.duq.edu/simon/Fall04/notes-6-20/node3.html
- http://www.doc.ic.ac.uk/~sgc/teaching/pre2012/v231/lecture9.html
- http://rmarcus.info/blog/2015/09/02/vulcan.html
- http://ocw.mit.edu/courses/electrical-engineering-and-computer-science/6-825-techniques-in-artificial-intelligence-sma-5504-fall-2002/lecture-notes/Lecture9Final.pdf
- https://books.google.com/books?id=xwBDylHhJhYC&pg=PA42&lpg=PA42&dq=demodulation+rule&source=bl&ots=WSHLneBzT0&sig=L-EuivNrxiG5GQjRRO40kiARO7o&hl=en&sa=X&ved=0CEYQ6AEwBmoVChMIydKL19K4yAIVCd9jCh1F6A9T#v=onepage&q=demodulation%20rule&f=false
-}

-- Steps to simplify to CNF
-- 1. Sentence, replace ->
-- 2. Move not inwards with De Morgan's laws
-- 3. Rename variables
-- 4. Move quantifiers out*
-- 5. Skolemize existentials
-- 6. Distribute ^ over v
-- 7. Flatten

{-

TODO List:
1. Better variable renaming skillz
2. Unification algorithm check
3. Paramodulation
-}

module Eddie (
    Sentence(..),
    Term(..),
    Name(..),
    Predicate(..),
    Clause(..),
    simplify,
    sentenceToClauses,
    prove,
    prove',
    ask,
    ask',
    displayProof
) where

import Data.List
import Data.Maybe(isJust)
import qualified Data.Map as Map
import qualified Data.Set as Set


-- Abstracted because I want to make these guys interned symbols sometime.
data Name = Name String deriving (Eq, Ord, Show)


-- Terms are things that can live in predicates
data Term =
      Function Name [Term] -- a literal is a nil-adic function
    | Variable Name
    deriving (Eq, Ord, Show)

data Predicate = Predicate Name [Term]
                 deriving (Eq, Ord, Show)

data Sentence =
      And Sentence Sentence
    | Or Sentence Sentence
    | Not Sentence
    | Implies Sentence Sentence
    | Iff Sentence Sentence
    | Forall Name Sentence
    | Exists Name Sentence
    | Pred Predicate
    deriving (Eq, Show)

type Binding = Map.Map Name Term


data Clause = Clause { positivePreds :: Set.Set Predicate
                      ,negativePreds :: Set.Set Predicate
                      ,proof         :: Proof }
                      deriving (Show)

data Proof = Axiom String
           | Resolution Clause Clause Binding
           | Paramodulation Clause Clause
             deriving (Eq, Show)


class TeXible a where
    texify :: a -> String
    -- stringify :: a -> String

unicodeAnd     = " \x2227 "
unicodeOr      = " \x2228 "
unicodeNot     = "\x00ac"
unicodeImplies = " \x2192 "
unicodeIff     = " \x2194 "
unicodeForall  = "\x2200"
unicodeExists  = "\x2203"
unicodeTrue    = "\x22a4"
unicodeFalse   = "\x22a5"

instance TeXible Sentence where
    texify (And a b)     = "(" ++ (texify a) ++ unicodeAnd ++ (texify b) ++ ")"
    texify (Or  a b)     = "(" ++ (texify a) ++ unicodeOr  ++ (texify b) ++ ")"
    texify (Not a)       = unicodeNot ++ (texify a)
    texify (Implies a b) = "(" ++ (texify a) ++ unicodeImplies ++ (texify b) ++ ")"
    texify (Iff a b)     = "(" ++ (texify a) ++ unicodeIff     ++ (texify b) ++ ")"
    texify (Forall a b)  = unicodeForall ++ (texify a) ++ " " ++ (texify b)
    texify (Exists a b)  = unicodeExists ++ (texify a) ++ " " ++ (texify b)
    texify (Pred p)      = texify p

instance TeXible Predicate where
    texify (Predicate (Name "Eq") [l, r]) =
        "\\left(" ++ (texify l) ++ " = " ++ (texify r) ++ "\\right)"
    texify (Predicate (Name n) t) =
        "\\mathtt{"++n++"}" ++ "\\left[" ++ (intercalate ", " (map texify t)) ++ "\\right]"

instance TeXible Term where
    texify (Variable (Name n)) = n
    texify (Function (Name n) t) = "\\text{"++n++"}" ++ "\\left(" ++  (intercalate ", " (map texify t)) ++ "\\right)"

instance TeXible Name where
    texify (Name v)  = v

instance (TeXible a, TeXible b) => TeXible (Map.Map a b) where
    texify b = "\\left\\{" ++ (intercalate "," (map (\(k, v) -> (texify k)++"\\leftarrow "++(texify v)) (Map.toList b))) ++"\\right\\}"

displayProof :: Clause -> String
displayProof c@(Clause _ _ (Axiom a)) = "\\frac{\\text{"++a++"}}{"++(texify c)++"}A"
displayProof c@(Clause _ _ (Resolution a b x)) = "\\frac{"++ (displayProof a) ++" \\; "++ (displayProof b) ++"}{"++(texify c)++"}R"++(texify x)
displayProof c@(Clause _ _ (Paramodulation a b)) = "\\frac{"++ (displayProof a) ++" \\; "++ (displayProof b) ++"}{"++(texify c)++"}P"

instance TeXible Clause where
    texify (Clause a b p) =
        if (null a && null b) then "\\bot" else
            "\\left(" ++
            intercalate "\\vee "
                ((map texify (Set.toList a)) ++ (map (("\\neg " ++) . texify) (Set.toList b))) ++
                "\\right) "
            -- ++ (texify p)

instance Eq Clause where
    (Clause p1 n1 _) == (Clause p2 n2 _) = p1==p2 && n1==n2

emptyClause :: Clause -> Bool
emptyClause (Clause a b _) = (null a && null b)

answerClause :: Clause -> Maybe (Term, Clause)
answerClause c@(Clause a b pf) = if (null b) && (Set.size a == 1) then
                                  (case Set.elemAt 0 a of
                                    Predicate (Name "Answer") [x] -> Just (x, c)
                                    _                      -> Nothing)
                              else
                                  Nothing

instance Ord Clause where
    (Clause a1 a2 _) <= (Clause b1 b2 _) = (length a1)+(length a2) <= (length b1)+(length b2)

instance TeXible Proof where
    texify (Axiom x) = x
    texify (Resolution a b c) = "{"++(texify a)++"@"++(texify b)++"}"++(texify c)










sentenceMap :: (Sentence -> Sentence) -> Sentence -> Sentence
sentenceMap f (And a b)     = And (f a) (f b)
sentenceMap f (Or  a b)     = Or  (f a) (f b)
sentenceMap f (Not a)       = Not (f a)
sentenceMap f (Implies a b) = Implies (f a) (f b)
sentenceMap f (Iff a b)     = Iff (f a) (f b)
sentenceMap f (Forall a b)  = Forall a (f b)
sentenceMap f (Exists a b)  = Exists a (f b)
sentenceMap _ (Pred (Predicate a t)) = (Pred (Predicate a t))

replaceArrows :: Sentence -> Sentence
replaceArrows (Implies a b) = replaceArrows (Or (Not a) b)
replaceArrows (Iff a b)     = replaceArrows (And (Implies a b) (Implies b a))
replaceArrows s             = sentenceMap replaceArrows s

deMorgan :: Sentence -> Sentence
deMorgan (Not (And a b)) = deMorgan (Or  (Not a) (Not b))
deMorgan (Not (Or  a b)) = deMorgan (And (Not a) (Not b))
deMorgan (Not (Not a))   = deMorgan a
deMorgan (Not (Forall a b)) = deMorgan (Exists a (Not b))
deMorgan (Not (Exists a b)) = deMorgan (Forall a (Not b))
deMorgan s = sentenceMap deMorgan s



skolemReplaceSentence :: Name -> Term -> Sentence -> Sentence
skolemReplaceSentence n t (Pred (Predicate p a)) =
    (Pred (Predicate p (map (skolemReplaceTerm n t) a)))
skolemReplaceSentence n t s = sentenceMap (skolemReplaceSentence n t) s

skolemReplaceTerm :: Name -> Term -> Term -> Term
skolemReplaceTerm n t (Function f a) =
    (Function f (map (skolemReplaceTerm n t) a))
skolemReplaceTerm n t (Variable a) = if n == a then t else (Variable a)

skolemize :: [Name] -> Sentence -> Sentence
skolemize universe (Forall a b) = skolemize (a:universe) b
skolemize universe (Exists (Name n) b) =
    skolemReplaceSentence
        (Name n)
        (Function (Name (n++"*"))
                  (map (\name -> (Variable name)) universe))
        (skolemize universe b)
skolemize universe s = sentenceMap (skolemize universe) s

distribute :: Sentence -> Sentence
distribute (Or (And a b) c) = distribute (And (Or a c) (Or b c))
distribute (Or c (And a b)) = distribute (And (Or a c) (Or b c))
-- FIXME and find out why sentenceToClauses didn't bork!
distribute s = let s' = sentenceMap distribute s in
                   if s' == s then s' else distribute s'


simplify :: Sentence -> Sentence
simplify s = distribute $ skolemize [] $ deMorgan $ replaceArrows s


sentenceToClauses :: String -> Sentence -> [Clause]
sentenceToClauses n (And a b) = (sentenceToClauses n a) ++ (sentenceToClauses n b)
sentenceToClauses n (Not (Pred a))   = [Clause
                                      {positivePreds = Set.empty,
                                       negativePreds = Set.singleton a,
                                       proof         = Axiom n}]
sentenceToClauses n (Pred a)   = [Clause
                                {positivePreds = Set.singleton a,
                                 negativePreds = Set.empty,
                                 proof         = Axiom n}]
-- Add assertions to make sure you're `head`ing a singleton list. Otherwise bad
-- bugs go uncaught! Like the distribute bug.
-- FIXME
sentenceToClauses n (Or a b)  = [Clause
                               {positivePreds =
                                (positivePreds (head $ sentenceToClauses n a) `Set.union`
                                 positivePreds (head $ sentenceToClauses n b)),
                                negativePreds =
                                (negativePreds (head $ sentenceToClauses n a) `Set.union`
                                 negativePreds (head $ sentenceToClauses n b)),
                                proof         = Axiom n}]

-- Ordered resolution (noncommutative!)
resolve :: Clause -> Clause -> [Clause]
resolve c1@(Clause p1 n1 pf1)
        c2@(Clause p2 n2 pf2) =
    [case unifyPredicates ps ns of
        Just b -> clauseApplyBinding b (Clause  ((Set.delete ps p1) `Set.union` p2)
                                          ((Set.delete ns n2) `Set.union` n1)
                                          (Resolution c1 c2 b))
        | ps <- Set.toList p1, ns <- Set.toList n2, isJust $ unifyPredicates ps ns]

{-
-- Ordered resolution (noncummutative!)
-- Note the difference between this and the one above.
-- If S := P || !P || Q, then Resolve(S, S) is NOT Q... :(
resolve :: Clause -> Clause -> [Clause]
resolve c1@(Clause p1 n1 pf1)
        c2@(Clause p2 n2 pf2) =
    [case unifyPredicates ps ns of
        Just b -> clauseApplyBinding b (Clause  ((Set.delete ps (p1 `Set.union` p2)))
                                          ((Set.delete ns (n2 `Set.union` n1)))
                                          (Resolution c1 c2))
        | ps <- Set.toList p1, ns <- Set.toList n2, isJust $ unifyPredicates ps ns]
-}



isEquality :: Predicate -> Bool
isEquality (Predicate (Name "Eq") _) = True
isEquality _ = False

diag :: (Term -> [(Term, Binding)]) -> [Term] -> [([Term], Binding)]
diag f [] = []
diag f (x:xs) = let r = f x in
                    (map (\(t, b) -> (t:xs, b)) r)++
                    (map (\(l, b) -> (x:l , b)) (diag f xs))

allReplacementsPred :: Term -> Term -> Predicate -> [(Predicate, Binding)]
allReplacementsPred search replace p@(Predicate n r) =
    map (\(t, b) -> ((Predicate n t), b)) $
        diag (allReplacements search replace) r

allReplacements :: Term -> Term -> Term -> [(Term, Binding)]
allReplacements search replace v@(Variable _) =
    case unifyTerms Map.empty v search of
        Nothing -> []
        Just b  -> [(replace, b)]

allReplacements search replace f@(Function n r) =
    (case unifyTerms Map.empty f search of
        Nothing -> []
        Just b  -> [(replace, b)]) ++
    (map (\(t, b) -> ((Function n t), b)) $ diag (allReplacements search replace) r)

paramodulate :: Clause -> Clause -> [Clause]
paramodulate c1@(Clause p1 n1 pf1)
             c2@(Clause p2 n2 pf2) =
    (concat
        [map (\(t, b) -> clauseApplyBinding b $
                Clause (Set.insert t ((Set.delete ps p2) `Set.union` (Set.delete e p1)))
                       (n1 `Set.union` n2)
                       (Paramodulation c1 c2))
             ((allReplacementsPred l r ps)++(allReplacementsPred r l ps))
            | e@(Predicate _ [l, r]) <- filter isEquality $ Set.toList p1,
              ps <- Set.toList p2])
    ++
    (concat
        [map (\(t, b) -> clauseApplyBinding b $
                Clause (p2 `Set.union` (Set.delete e p1))
                       (Set.insert t ((Set.delete ps n2) `Set.union` n2))
                       (Paramodulation c1 c2))
             ((allReplacementsPred l r ps)++(allReplacementsPred r l ps))
            | e@(Predicate _ [l, r]) <- filter isEquality $ Set.toList p1,
              ps <- Set.toList n2])

prove' :: [Clause] -> [Clause] -> Clause
prove' cmp cls = case (concat [(resolve a b)++(resolve b a)++
                               (paramodulate a b)++(paramodulate b a)
                               | a <- cmp, b <- cls]) \\ (cmp++cls) of
                    [] -> Clause
                            Set.empty
                            Set.empty
                            (Axiom "Failed: Exhaustive search.")
                    r  -> (case find emptyClause r of
                            Nothing   -> prove' (sort (nub (cmp++cls++r))) (nub r)
                            Just c    -> c)

prove :: [Clause] -> Clause
prove x = prove' x x


ask' :: [Clause] -> [Clause] -> Maybe (Term, Clause)
ask' cmp cls = case (nub $ concat [(resolve a b)++(resolve b a)++
                                   (paramodulate a b)++(paramodulate b a)
                                  | a <- cmp, b <- cls]) \\ cmp of
                  [] -> Nothing
                  r  -> (case find isJust (map answerClause r) of
                          Nothing               -> ask' (nub (cmp++cls++r)) r
                          Just x                -> x)

-- Return the value X of Answer[X].
ask :: [Clause] -> Maybe (Term, Clause)
ask x = ask' x x


-- Unification is based on Martelli, Montanari (1982), with Norvig's
-- correction. See
--  [1] http://moscova.inria.fr/~levy/courses/X/IF/03/pi/levy2/martelli-montanari.pdf
--  [2] http://norvig.com/unify-bug.pdf

unifyPredicates :: Predicate -> Predicate -> Maybe Binding
unifyPredicates (Predicate n1 ts1) (Predicate n2 ts2) =
    if n1 /= n2 then Nothing else
        if length ts1 /= length ts2 then Nothing else
            foldl (\oldbin (a1, a2) ->
                        maybe
                            Nothing
                            (\ob -> unifyTerms ob a1 a2)
                            oldbin)
                  (Just Map.empty) (zip ts1 ts2)

-- This is not happening.
-- FIXME
occursCheck :: Name -> Term -> Bool
occursCheck n (Function a args) = any (occursCheck n) args
occursCheck n (Variable v) = v == n

unifyTerms :: Binding -> Term -> Term -> Maybe Binding
unifyTerms b (Variable v) x =
    case (x, Map.lookup v b) of
        (_, Just x') -> unifyTerms b x x'
        (Variable w, Nothing) ->
            if v == w then (Just b) else
                if Map.member w b then unifyTerms b x (Variable v) else
                    Just (Map.insert v x b) 
        (_, Nothing) -> if occursCheck v (applyBinding b x) then Nothing else Just (Map.insert v x b)
--                                          ^ need this for recursive ooblech prevention

unifyTerms b x (Variable v) = unifyTerms b (Variable v) x

unifyTerms b (Function f1 a1) (Function f2 a2) =
    if f1 /= f2 then Nothing else
        if length a1 /= length a2 then Nothing else
            foldl (\oldbin (a'1, a'2) ->
                        maybe
                            Nothing
                            (\ob -> unifyTerms ob a'1 a'2)
                            oldbin)
                  (Just b) (zip a1 a2)

-- unifyTerms b t1 t2 = Nothing


clauseApplyBinding :: Binding -> Clause -> Clause
clauseApplyBinding b (Clause p n pf) = (Clause (Set.map (predicateApplyBinding b) p)
                                               (Set.map (predicateApplyBinding b) n)
                                               pf)

predicateApplyBinding :: Binding -> Predicate -> Predicate
predicateApplyBinding b (Predicate n args) = (Predicate n (map (applyBinding b) args))

-- Someday this will cause a lot of pain, because the order in which bindings
-- are applied is actually important.
-- FIXME
applyBinding :: Binding -> Term -> Term
-- applyBinding b t = Map.foldrWithKey skolemReplaceTerm t b
applyBinding b t = foldl (\t' (n, v) -> skolemReplaceTerm n v t') t (Map.toList b)
