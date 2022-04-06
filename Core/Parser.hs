{-# LANGUAGE PatternGuards, TupleSections, ViewPatterns #-}
module Core.Parser (parse) where

import Core.Syntax
import Core.Prelude

import Name hiding (freshName)
import qualified Name
import StaticFlags
import Utilities

import qualified Data.Map as M

import qualified Language.Haskell.Exts as LHE
import Language.Preprocessor.Cpphs

import System.Directory
import System.FilePath (replaceExtension)


parse :: FilePath -> IO (String, [(Var, Term)])
parse path = do
    -- Read and pre-process .core file
    contents <- readFile path >>= cpp
    unless qUIET $ putStrLn contents
    
    -- Read and pre-process corresponding .hs file (if any)
    let wrapper_path = replaceExtension path ".hs"
    has_wrapper <- doesFileExist wrapper_path
    wrapper <- if has_wrapper then readFile wrapper_path >>= cpp else return ""
    
    -- Return parsed .core file
    return (wrapper, moduleCore . LHE.fromParseResult . LHE.parseFileContentsWithMode (LHE.defaultParseMode { LHE.parseFilename = path, LHE.extensions = [LHE.EnableExtension LHE.CPP, LHE.EnableExtension LHE.MagicHash] }) $ contents)
  where cpp = runCpphs (defaultCpphsOptions { boolopts = (boolopts defaultCpphsOptions) { locations = False }, defines = ("SUPERCOMPILE", "1") : defines defaultCpphsOptions }) path


data ParseState = ParseState {
    ids :: IdSupply,
    dc_wrappers :: M.Map DataCon Var,
    int_wrappers :: M.Map Integer Var,
    char_wrappers :: M.Map Char Var,
    prim_wrappers :: M.Map PrimOp Var
  }

initParseState :: ParseState
initParseState = ParseState {
    ids = parseIdSupply,
    dc_wrappers = M.empty,
    int_wrappers = M.empty,
    char_wrappers = M.empty,
    prim_wrappers = M.empty
  }

buildWrappers :: ParseState -> [(Var, Term)]
buildWrappers ps
  = [ (f, lambdas xs $ data_ dc xs)
    | (dc, f) <- M.toList (dc_wrappers ps)
    , let arity = dataConArity dc; xs = map (\i -> name $ "x" ++ show i) [1..arity] ] ++
    [ (f, int i)
    | (i, f) <- M.toList (int_wrappers ps) ] ++
    [ (f, char c)
    | (c, f) <- M.toList (char_wrappers ps) ] ++
    [ (f, lam (name "x1") $ lam (name "x2") $ primOp pop [var (name "x1"), var (name "x2")])
    | (pop, f) <- M.toList (prim_wrappers ps) ] ++
    [ (name "error", lam (name "msg") $ case_ (var (name "prelude_error") `app` name "msg") []) ]
  where
    dataConArity "()"      = 0
    dataConArity "(,)"     = 2
    dataConArity "(,,)"    = 3
    dataConArity "(,,,)"   = 4
    dataConArity "[]"      = 0
    dataConArity "(:)"     = 2
    dataConArity "Left"    = 1
    dataConArity "Right"   = 1
    dataConArity "True"    = 0
    dataConArity "False"   = 0
    dataConArity "Just"    = 1
    dataConArity "Nothing" = 0
    dataConArity "MkU"     = 1 -- GHCBug
    dataConArity "Z"       = 0 -- Exp3_8
    dataConArity "S"       = 1 -- Exp3_8
    dataConArity "Leaf"    = 1 -- SumTree
    dataConArity "Branch"  = 2 -- SumTree
    dataConArity "Empty"   = 0 -- ZipTreeMaps
    dataConArity "Node"    = 3 -- ZipTreeMaps
    dataConArity "Wheel1"  = 2 -- Wheel-Sieve1
    dataConArity "Wheel2"  = 3 -- Wheel-Sieve2
    dataConArity "A"       = 0 -- KMP
    dataConArity "B"       = 0 -- KMP
    dataConArity s = panic "dataConArity" (text s)

newtype ParseM a = ParseM { unParseM :: ParseState -> (ParseState, a) }

instance Functor ParseM where
    fmap = liftM

instance Applicative ParseM where
  pure x = ParseM $ \s -> (s, x)
  fab <*> fa = ParseM $ \s -> case (unParseM fab) s of (s', ab) -> case (unParseM fa) s' of (s'', a) -> (s'', ab a)  

instance Monad ParseM where
    return x = ParseM $ \s -> (s, x)
    mx >>= fxmy = ParseM $ \s -> case unParseM mx s of (s, x) -> unParseM (fxmy x) s

freshName :: String -> ParseM Name
freshName n = ParseM $ \s -> let (ids', x) = Name.freshName (ids s) n in (s { ids = ids' }, x)

freshFloatName :: String -> Term -> ParseM (Maybe (Var, Term), Name)
freshFloatName _ (Term (Var x)) = return (Nothing, x)
freshFloatName n e              = freshName n >>= \x -> return (Just (x, e), x)

nameIt :: Term -> (Var -> ParseM Term) -> ParseM Term
nameIt e f = freshFloatName "a" e >>= \(mb_float, x) -> fmap (bind (maybeToList mb_float)) $ f x

nameThem :: [Term] -> ([Var] -> ParseM Term) -> ParseM Term
nameThem es f = mapM (freshFloatName "a") es >>= \(unzip -> (mb_es, xs)) -> fmap (bind (catMaybes mb_es)) $ f xs

list :: [Term] -> ParseM Term
list es = nameThem es $ \es_xs -> replicateM (length es) (freshName "list") >>= \cons_xs -> return $ uncurry bind $ foldr (\(cons_x, e_x) (floats, tl) -> ((cons_x, tl) : floats, cons e_x cons_x)) ([], nil) (cons_xs `zip` es_xs)

dataConWrapper :: DataCon -> ParseM Var
dataConWrapper = grabWrapper dc_wrappers (\s x -> s { dc_wrappers = x })

intWrapper :: Integer -> ParseM Var
intWrapper = grabWrapper int_wrappers (\s x -> s { int_wrappers = x })

charWrapper :: Char -> ParseM Var
charWrapper = grabWrapper char_wrappers (\s x -> s { char_wrappers = x })

primWrapper :: PrimOp -> ParseM Var
primWrapper = grabWrapper prim_wrappers (\s x -> s { prim_wrappers = x })

grabWrapper :: Ord a
            => (ParseState -> M.Map a Var) -> (ParseState -> M.Map a Var -> ParseState)
            -> a -> ParseM Var
grabWrapper get set what = do
    mb_x <- ParseM $ \s -> (s, M.lookup what (get s))
    case mb_x of Just x -> return x
                 Nothing -> freshName "wrap" >>= \x -> ParseM $ \s -> (set s (M.insert what x (get s)), x)

runParseM :: ParseM a -> ([(Var, Term)], a)
runParseM = first buildWrappers . flip unParseM initParseState


moduleCore :: Show l => LHE.Module l -> [(Var, Term)]
moduleCore (LHE.Module _loc _name _ops  _imports decls) = wrap_xes ++ xes
  where (wrap_xes, xes) = runParseM $ declsCore decls


declsCore :: Show l => [LHE.Decl l] -> ParseM [(Name, Term)]
declsCore = fmap concat . mapM declCore

declCore :: Show l => LHE.Decl l -> ParseM [(Name, Term)]
declCore (LHE.FunBind _ [LHE.Match _loc n pats (LHE.UnGuardedRhs _ e) binds]) = do
    let x = name (nameString n)
        (ys, _bound_ns, build) = patCores pats
    e <- expCore e
    case binds of
      Just (LHE.BDecls _ where_decls) -> do
        xes <- declsCore where_decls
        return [(x, lambdas ys $ build $ bind xes e)]
      Nothing -> return [(x, lambdas ys $ build e)]
declCore (LHE.PatBind _loc pat (LHE.UnGuardedRhs _ e) binds) = do
    let (x, bound_ns, build) = patCore pat
    e <- expCore e
    case binds of
      Just (LHE.BDecls _ where_decls) -> do
        xes <- declsCore where_decls
        return $ (x, bind xes e) : [(n, build (var n)) | n <- bound_ns, n /= x]
      Nothing -> return $ (x, e) : [(n, build (var n)) | n <- bound_ns, n /= x]
declCore d = panic "declCore" (text $ show d)

expCore :: Show l => LHE.Exp l -> ParseM Term
expCore (LHE.Var _ qname) = qNameCore qname
expCore (LHE.Con _ qname) = fmap var $ dataConWrapper $ qNameDataCon qname
expCore (LHE.Lit _ lit) = literalCore lit
expCore (LHE.NegApp l e) = expCore $ LHE.App l (LHE.Var l (LHE.UnQual l (LHE.Ident l "negate"))) e
expCore (LHE.App _ e1 e2) = expCore e2 >>= \e2 -> e2 `nameIt` \x2 -> fmap (`app` x2) $ expCore e1
expCore (LHE.InfixApp _ e1 eop e2) = expCore e1 >>= \e1 -> e1 `nameIt` \x1 -> expCore e2 >>= \e2 -> e2 `nameIt` \x2 -> qopCore eop >>= \eop -> return $ apps eop [x1, x2]
expCore (LHE.Let _ (LHE.BDecls _ binds) e) = do
    xes <- declsCore binds
    fmap (bind xes) $ expCore e
expCore (LHE.If _ e1 e2 e3) = expCore e1 >>= \e1 -> liftM2 (if_ e1) (expCore e2) (expCore e3)
expCore (LHE.Case _ e alts) = expCore e >>= \e -> fmap (case_ e) (mapM altCore alts)
expCore (LHE.Tuple _ LHE.Boxed es) = mapM expCore es >>= flip nameThem (return . tuple)
expCore (LHE.Paren _ e) = expCore e
expCore (LHE.List _ es) = mapM expCore es >>= list
expCore (LHE.Lambda _ ps e) = expCore e >>= \e -> return $ lambdas xs $ build e
  where (xs, _bound_xs, build) = patCores ps
expCore (LHE.LeftSection _ e1 eop) = expCore e1 >>= \e1 -> e1 `nameIt` \x1 -> qopCore eop >>= \eop -> return (eop `app` x1) -- NB: careful about sharing if you add Right sections!
expCore (LHE.EnumFromThen l e1 e2) = expCore $ LHE.App l (LHE.App l (LHE.Var l (LHE.UnQual l (LHE.Ident l "enumFromThen"))) e1) e2
expCore e = panic "expCore" (text $ show e)

qopCore :: Show l => LHE.QOp l -> ParseM Term
qopCore (LHE.QVarOp _ qn) = qNameCore qn
qopCore (LHE.QConOp _ qn) = qNameCore qn

literalCore :: LHE.Literal l -> ParseM Term
literalCore (LHE.Int _ i _) = fmap var $ intWrapper i
literalCore (LHE.Char _ c _) = fmap var $ charWrapper c
literalCore (LHE.String l s st) = mapM (literalCore . (\x -> LHE.Char l x st)) s >>= list

altCore :: Show l => LHE.Alt l -> ParseM Alt
altCore (LHE.Alt _loc pat (LHE.UnGuardedRhs _ e) Nothing) = do
    e <- expCore e
    return (altcon, build e)
  where (altcon, build) = altPatCore pat
altCore (LHE.Alt _loc pat (LHE.UnGuardedRhs _ e) (Just (LHE.BDecls _ binds))) = do
    xes <- declsCore binds
    e <- expCore e
    return (altcon, build (bind xes e))
  where (altcon, build) = altPatCore pat

altPatCore :: Show l => LHE.Pat l -> (AltCon, Term -> Term)
altPatCore (LHE.PApp _ qname pats)           = dataAlt (qNameDataCon qname) (patCores pats)
altPatCore (LHE.PInfixApp _ pat1 qname pat2) = dataAlt (qNameDataCon qname) (patCores [pat1, pat2])
altPatCore (LHE.PTuple _ LHE.Boxed [pat1, pat2])       = dataAlt pairDataCon (patCores [pat1, pat2])
altPatCore (LHE.PParen _ pat)                = altPatCore pat
altPatCore (LHE.PList _ [])                  = dataAlt nilDataCon ([], [], id)
altPatCore (LHE.PLit _ (LHE.Signless _) (LHE.Int _ i _))          = (LiteralAlt (Int i), id)
altPatCore (LHE.PWildCard _)                   = (DefaultAlt Nothing, id)
altPatCore p = panic "altPatCore" (text $ show p)

dataAlt :: DataCon -> ([Var], [Var], Term -> Term) -> (AltCon, Term -> Term)
dataAlt dcon (names, _bound_ns, build) = (DataAlt dcon names, build)


specialConDataCon :: LHE.SpecialCon l -> DataCon
specialConDataCon (LHE.UnitCon _) = unitDataCon
specialConDataCon (LHE.ListCon _) = nilDataCon
specialConDataCon (LHE.TupleCon _ LHE.Boxed 2) = pairDataCon
specialConDataCon (LHE.Cons _) = consDataCon

nameString :: LHE.Name l -> String
nameString (LHE.Ident _ s)  = s
nameString (LHE.Symbol _ s) = s

qNameCore :: Show l => LHE.QName l -> ParseM Term
qNameCore (LHE.UnQual _ n) = fmap var $ case nameString n of
    "+"   -> primWrapper Add
    "-"   -> primWrapper Subtract
    "*"   -> primWrapper Multiply
    "div" -> primWrapper Divide
    "mod" -> primWrapper Modulo
    "=="  -> primWrapper Equal
    "<"   -> primWrapper LessThan
    "<="  -> primWrapper LessThanEqual
    s -> return (name s)
qNameCore (LHE.Special _ sc) = fmap var $ dataConWrapper $ specialConDataCon sc
qNameCore qn = panic "qNameCore" (text $ show qn)

qNameDataCon :: LHE.QName l -> DataCon
qNameDataCon (LHE.UnQual _ name) = nameString name
qNameDataCon (LHE.Special _ sc)  = specialConDataCon sc

patCores :: Show l => [LHE.Pat l] -> ([Var], [Var], Term -> Term)
patCores []     = ([], [], id)
patCores (p:ps) = (n':ns', bound_ns' ++ bound_nss', build . build')
  where (n', bound_ns', build) = patCore p
        (ns', bound_nss', build') = patCores ps

-- TODO: this function is a hilarious shadowing bug waiting to happen. Thread the IdSupply in here to generate temp names.
patCore :: Show l
        => LHE.Pat l      -- Pattern
        -> (Var,          -- Name consumed by the pattern
            [Var],        -- Names bound by the pattern
            Term -> Term) -- How to build the (strict) consuming context around the thing inside the pattern
patCore (LHE.PVar _ n)    = (x, [x], id)
  where x = name (nameString n)
patCore (LHE.PWildCard _) = (x, [x], id)
  where x = name "_"
patCore (LHE.PParen _ p)  = patCore p
patCore (LHE.PTuple _ LHE.Boxed ps) = case tupleDataCon (length ps) of
    Nothing | [p] <- ps -> patCore p
    Just dc -> (n', bound_ns', \e -> case_ (var n') [(DataAlt dc ns', build e)])
      where n' = name "tup"
            (ns', bound_ns', build) = patCores ps
patCore (LHE.PInfixApp _ p1 qinfix p2) = (n', bound_ns1 ++ bound_ns2, \e -> case_ (var n') [(DataAlt (qNameDataCon qinfix) [n1', n2'], build1 (build2 e))])
  where n' = name "infx"
        (n1', bound_ns1, build1) = patCore p1
        (n2', bound_ns2, build2) = patCore p2
patCore (LHE.PApp _ (LHE.Special _ (LHE.UnitCon _)) []) = (name "unit", [], id)
patCore p = panic "patCore" (text $ show p)

bind :: [(Var, Term)] -> Term -> Term
bind xes e = letRec xes e
