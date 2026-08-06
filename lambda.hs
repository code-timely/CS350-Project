import Data.List ( find, nub )

-- Q1 Data Types -------------------------------------------------------------------------------------------------------------------------------------

type Var = String

data Lt = Variable Var | Term Lt Lt | Lambda Var Lt  


-- Q2 λ terms ----------------------------------------------------------------------------------------------------------------------------------------

-- (λc.cc)
a = Lambda "c" (Term (Variable "c") (Variable "c"))

-- (λc.cd)
b = Lambda "c" (Term (Variable "c") (Variable "d"))

-- (λx.xy)(λy.xy)
c = Term (Lambda "x" (Term (Variable "x") (Variable "y"))) (Lambda "y" (Term (Variable "x") (Variable "y")))

-- (λy.x)y
d = Term (Lambda "y" (Variable "x")) (Variable "y")

-- (λy.x)a
e = Term (Lambda "y" (Variable "x")) (Variable "a")


-- Q3 pretty printing routine -------------------------------------------------------------------------------------------------------------------------
instance Show Lt where
    show a = pretty_print a
        where 
            pretty_print (Variable a) = a
            pretty_print (Lambda a b) = "λ" ++ a ++ ". " ++ pretty_print b 
            pretty_print (Term a b) = "(" ++ (pretty_print a) ++ ")" ++ "(" ++ (pretty_print b) ++ ")"




--Q4 Subsititution  -----------------------------------------------------------------------------------------------------------------------------------

-- Helper function to get all the free variables of a λ term
freeVars (Variable var) = [var]
freeVars (Term t1 t2) = nub (freeVars t1 ++ freeVars t2)
freeVars (Lambda var term) = filter (/= var) (freeVars term)


-- MAIN function to enable substitution
subs (Variable a) x lt
    | x == a = lt
    | otherwise = Variable a
subs (Lambda var term) x lt
  | var == x = Lambda var term
  | elem var (freeVars lt) = error $ "Variable Capture is occuring"
  | otherwise = Lambda var (subs term x lt)
subs (Term t1 t2) x lt = Term (subs t1 x lt) (subs t2 x lt)




-- Q5 ß reduction using substition mechanishm ------------------------------------------------------------------------------------------------------------
betaReduce (Variable var) = Variable var
betaReduce (Lambda var term) = Lambda var (betaReduce term)
betaReduce (Term (Lambda var term) subterm) = betaReduce (subs term var subterm)

betaReduce (Term t1 t2) =
    let t1_red = betaReduce t1 in
        case t1_red of
            Lambda var t -> betaReduce (Term t1_red t2)
            _ -> Term t1_red (betaReduce t2)


-- Question 6 α - renaming -------------------------------------------------------------------------------------------------------------------------------

-- candidates: "a".."z", then "a'","b'",.. then "a''","b''" -> lazy eval ROX!!
candidates = [ [c] | c <- ['a'..'z'] ] ++ [ base ++ replicate k '\'' | k <- [1..], base <- map (:[]) ['a'..'z'] ]

-- helper function to get the first variable NOT in used from among candidates 
freshVar used = head $ filter (`notElem` used) candidates

-- helper function to get all occuring variables in a λ term
totalVar (Variable v) = [v]
totalVar (Lambda v term) = nub (v : totalVar term)
totalVar (Term t1 t2) = nub(totalVar t1 ++ totalVar t2)


-- α - renamer function
alphaRename (Variable v) old new
    | v == old  = Variable new
    | otherwise = Variable v
alphaRename (Lambda v term) old new
    | v == old = Lambda new (alphaRename term old new)
    | otherwise = Lambda v (alphaRename term old new)
alphaRename (Term a b) old new = Term (alphaRename a old new) (alphaRename b old new)

genVar term1 term2 = freshVar (nub (totalVar term1 ++ totalVar term2))

-- new substitution with α - renaming 

substitute_alpha (Variable a) x lt
    | x == a = lt
    | otherwise = Variable a

substitute_alpha (Lambda var term) x lt
    | var == x = Lambda var term
    | elem var (freeVars lt) =
        let new = genVar (Lambda var term) lt
            renamedBody = alphaRename term var new 
        in Lambda new (substitute_alpha renamedBody x lt)
    | otherwise = Lambda var (substitute_alpha term x lt)

substitute_alpha (Term t1 t2) x lt = Term (substitute_alpha t1 x lt) (substitute_alpha t2 x lt)

-- Q7 ß-reduction with  α - renaming ------------------------------------------------------------------------------------------------------------------------

betaReduce_alpha (Variable var) = Variable var
betaReduce_alpha (Lambda var term) = Lambda var (betaReduce_alpha term)
betaReduce_alpha (Term (Lambda var term) subterm) = betaReduce_alpha (substitute_alpha term var subterm)

betaReduce_alpha (Term t1 t2) =
    let t1_red = betaReduce_alpha t1 in
        case t1_red of
            Lambda var t -> betaReduce_alpha (Term t1_red t2)
            _ -> Term t1_red (betaReduce_alpha t2)

--------------------------------------------------------------------------------------------------------------------------------------------------------------

-- Some test cases on which we tried 

(@@) = Term -- for brevity

-- λx.λy.xy ->α λx.λz. xz

term1 = Lambda "x" (Lambda "y" (Variable "x" @@ Variable "y"))
talpha = alphaRename term1 "y" "z"
-- expected show: λx. λz. (x)(z)

-- (λx.λy.x) z -> λy.z
term2 = Lambda "x" (Lambda "y" (Variable "x")) @@ Variable "z"
tBeta1 = betaReduce_alpha term2
-- ex1pected show: λy. z

-- (λx.λy.xy) z -> λy.zy
term3 = (Lambda "x" (Lambda "y" (Variable "x" @@ Variable "y")) @@ Variable "z")
tBeta2 = betaReduce_alpha term3
-- expected show: λy. (z)(y)

-- (λx.λy.xz) y -> (λy. xz)[x := y] ->α (λa. xz)[x := y] -> λa. yz
term4 = (Lambda "x" (Lambda "y" (Variable "x" @@ Variable "z")) @@ Variable "y")
tBetaAlpha = betaReduce_alpha term4
-- expected show: λa. (y)(z)

-- lecture example

-- M = λfx. f(fx)
m = Lambda "f" (Lambda "x" (Variable "f" @@ (Variable "f" @@ Variable "x")))
-- N = λy.xy
n = Lambda "y" (Variable "x" @@ Variable "y")

-- ß reduce (M N) N
tMNN = betaReduce_alpha ((m @@ n) @@ n)
-- expected show: (x)((x)(λy. (x)(y)))