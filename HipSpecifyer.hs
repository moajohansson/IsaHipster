-- Add HipSpec specifics to a Haskell file, containing a module which we assume is generated by 
-- Isabelle's code generator.

module Main where

import System.Environment
import Language.Haskell.Exts
import Language.Haskell.Exts.SrcLoc
import Debug.Trace
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set  
import Data.List
import Data.Data
import Data.Typeable
import Data.Maybe

process mode m =  
  if (mode == "Q") then (quickspecify m) 
  else if (mode == "H") then (hipspecify m)
  -- This is a really ugly way, will have a separate QuickSpecifyer when I can be bothered...
  else error "HipSpecifyer: Specify mode Q (QuikcSpec) or H (HipSpec)."
                                              
--hipspecfy :: ParseResult Module -> Module
hipspecify (ParseFailed loc err_msg) = error err_msg
hipspecify (ParseOk (Module srcloc modnm modprg warn exports imps decls)) =
  Module srcloc (ModuleName "Main") (pragma:modprg) warn exports (imp_ord:imps++imports) 
  (enumA:(concatMap (add_decls funs) decls) ++ [add_main decls True, defaultRecordDecl funs])
    where
      imports = map mk_importDecl ["HipSpec","Data.Typeable","Test.Feat"] 
      imp_ord = ImportDecl noLoc (ModuleName "Prelude") False False Nothing Nothing 
                (Just (False, [IAbs (Ident "Ord"),IAbs (Ident "Show")]))
      pragma = LanguagePragma noLoc (map Ident ["DeriveDataTypeable", "TemplateHaskell"]) 
      enumA = SpliceDecl noLoc (App (Con (UnQual (Ident "deriveEnumerable"))) ((TypQuote (UnQual (Ident "A")))))
      mk_importDecl moduleName = 
        ImportDecl noLoc (ModuleName moduleName) False False Nothing Nothing Nothing
      funs = nub (concat [ [ (name, typ) | name <- names ] | TypeSig _ names typ <- decls ])

defaultRecordDecl :: [(Name, Type)] -> Decl
defaultRecordDecl funs =
  DataDecl nowhere DataType [] (Ident "Default") [] [decl] []
  where
    decl = QualConDecl nowhere [] [] (RecDecl (Ident "Default") decls)
    decls = zipWith mkDecl [0..] funs
    mkDecl i (name, ty) = ([Ident ("default" ++ show i)], UnBangedTy ty)

nowhere :: SrcLoc
nowhere = SrcLoc "" 0 0

quickspecify (ParseFailed loc err_msg) = error err_msg
quickspecify (ParseOk (Module srcloc modnm modprg warn exports imps decls)) =
  Module srcloc (ModuleName "Main") (pragma:modprg) warn exports (imp_ord:imps++imports) 
  (enumA:(concatMap (add_decls []) decls) ++ [add_main decls False])
    where
      imports = map mk_importDecl ["Test.QuickCheck.Arbitrary","Test.QuickSpec","Data.Typeable", "HipSpec", "Test.Feat"] 
      imp_ord = ImportDecl noLoc (ModuleName "Prelude") False False Nothing Nothing 
                (Just (False, [IAbs (Ident "Ord"), IAbs (Ident "Show")]))
      pragma = LanguagePragma noLoc (map Ident ["DeriveDataTypeable", "TemplateHaskell"]) 
      enumA = SpliceDecl noLoc (App (Con (UnQual (Ident "deriveEnumerable"))) ((TypQuote (UnQual (Ident "A")))))
      mk_importDecl moduleName = 
        ImportDecl noLoc (ModuleName moduleName) False False Nothing Nothing Nothing
        
add_decls funs dec =
  case dec of 
    DataDecl loc dataOrNew context name tyVarBnds qualConDecls decls ->
      [DataDecl loc dataOrNew context name tyVarBnds qualConDecls (new_ders++decls),
       SpliceDecl noLoc (App (Con (UnQual (Ident "deriveEnumerable"))) ((TypQuote (UnQual name)))),
       InstDecl noLoc (ctxt tyVarBnds) (UnQual (Ident "Arbitrary")) 
                [foldr build_typApp (TyCon (UnQual name)) tyVarBnds] 
                [InsDecl (FunBind [Match noLoc (Ident "arbitrary") [] Nothing (UnGuardedRhs rhs) (BDecls [])])],
       InstDecl noLoc (ctxt2 tyVarBnds) (UnQual (Ident "CoArbitrary")) 
                [foldr build_typApp (TyCon (UnQual name)) tyVarBnds] 
                 [InsDecl (FunBind [Match noLoc (Ident "coarbitrary") [] Nothing 
                                    (UnGuardedRhs (Con (UnQual (Ident "coarbitraryShow")))) (BDecls [])])]
          
      ]
        where 
          new_ders = map ((\x -> (x,[])) . UnQual . Ident) ["Eq", "Ord", "Typeable", "Show"]
          ctxt tybnds = case tybnds of 
            [] -> [] 
            _ -> map (\v -> ClassA (UnQual (Ident "Enumerable")) [v]) (map tybinds2vars tybnds)
          ctxt2 tybnds = case tybnds of 
            [] -> [] 
            _ -> map (\v -> ClassA (UnQual (Ident "Show")) [v]) (map tybinds2vars tybnds)  
          build_typApp tybind ty =
            case tybind of 
              KindedVar nm _ -> TyApp ty (TyVar nm)
              UnkindedVar nm -> TyApp ty (TyVar nm) 
          tybinds2vars tybind = 
            case tybind of 
              KindedVar nm _ -> TyVar nm
              UnkindedVar nm -> TyVar nm    
          rhs = App (Con (UnQual (Ident "sized"))) (Con (UnQual (Ident "uniform")))   
    TypeSig loc names ty -> [TypeSig loc names (TyFun (TyCon (UnQual (Ident "Default"))) ty)]
    FunBind matches -> [FunBind (map (add_match funs) matches ++ [default_case funs matches])]
    _ -> [dec]

add_match funs (Match loc name pats Nothing rhs binds) =
  add_expr funs (Match loc name (PVar (Ident "defaultVar"):pats) Nothing rhs binds)

default_case funs (Match _ name pats _ _ _:_) =
  let Just i = elemIndex name (map fst funs)
      vars = map makeVar [0..length pats-1]
      makeVar n = Ident ("v" ++ show n)
      rhs = foldl App (App (Var (UnQual (Ident ("default" ++ show i)))) (Var (UnQual (Ident "defaultVar")))) (map (Var . UnQual) vars)
  in  Match nowhere name (map PVar (Ident "defaultVar":vars)) Nothing (UnGuardedRhs rhs) (BDecls [])

add_expr :: Data a => [(Name, Type)] -> a -> a
add_expr funs expr =
  case cast expr of
    Just e@(Var (UnQual name)) | name `elem` map fst funs ->
      fromJust (cast (App e (Var (UnQual (Ident "defaultVar")))))
    _ ->
      gmapT (add_expr funs) expr
 
-- HipSpec doesnt need a main anymore so we just add a dummy main function.   
add_main decls is_hipspec = 
  FunBind [Match noLoc (Ident "main") [] Nothing (UnGuardedRhs rhs) (BDecls [])] 
    where
      -- last arg should be a list, hipspec :: Signature a => FilePath -> a -> IO ()
      rhs = if is_hipspec then (Con (Qual (ModuleName "Prelude") (Ident "undefined"))) -- App (App (Con (UnQual (Ident "hipSpec"))) arg1) arg2
            else App (Con (UnQual (Ident "quickSpec"))) arg2
      -- arg1 = SpliceExp(ParenSplice (Con (UnQual (Ident "fileName")))) 
      arg2 = List (vars ++ constrs ++ funs)
      
      numVars = 3 -- number of vars of each type.
      
      --datatypeMap = foldr get_datatypes Map.empty decls
      --varsMap = Map.map (build_var_list numVars) datatypeMap
      --vars = (build_var_list numVars (TyCon (UnQual(Ident "A")))):(map snd (Map.toList varsMap))
        
      -- Datatype constructors to be used by QuickSpec
      typConstrMap = foldr get_constructors Map.empty decls
      constrs = map snd (Map.toList (Map.mapWithKey build_const_list typConstrMap))
      
      -- Function symbols to be used by QuickSpec
      (funTypSet,funConstMap) = foldr get_funTyps (Set.empty, Map.empty) decls
      funs = map snd (Map.toList (Map.mapWithKey build_const_list funConstMap))
      -- Make variables of types occuring in function arguments.
      vars = map (build_var_list numVars) (Set.toList funTypSet)



-- Make lists of variables for each datatype and give them to 'vars' function.
build_var_list num_vars typ =      
  (App (App (Con (UnQual (Ident "vars"))) varsList) type_thingy) 
  where
    varsList = List (map (\x -> Lit(String x)) (take num_vars (map (\x -> [x]) ['a'..'z'])))
    type_thingy = Paren(ExpTypeSig noLoc (Con (Qual (ModuleName "Prelude") (Ident "undefined"))) typ)

    
build_const_list :: Name -> (Int, Type) -> Exp
build_const_list name (num_args, typ) = 
  app (app (Con (UnQual (Ident ("fun"++ (show num_args))))) name_exp) type_expr
    where
      type_expr = Paren(ExpTypeSig noLoc (Con (UnQual name)) typ)
      name_exp = Lit (String(nameString name))
      nameString nm = 
        case nm of (Ident n) -> n 
                   (Symbol n) -> n
                   
-- All polymorphic types gets replaced by QuickSpec's monomorphic A-type.
quickSpecType = TyCon (UnQual (Ident "A"))                 

-- Monomorphise a type, inserting the above type instead.
monom ty = 
  case ty of
    TyForall _ _ t -> monom t
    TyFun t1 t2 -> TyFun (monom t1) (monom t2)
    TyTuple b ts -> TyTuple b (map monom ts)
    TyList t -> TyList (monom t)
    TyApp t1 t2 -> TyApp (monom t1) (monom t2)
    TyVar _ -> quickSpecType -- Gets rid of type variables
    TyParen t -> TyParen (monom t)
    TyInfix t1 nm t2 -> TyInfix (monom t1) nm (monom t2)
    TyKind t k -> TyKind (monom t) k 
    TyCon _ -> ty 
    
-- Arity of a Function type
arity ty = 
  case ty of
    TyForall _ _ t -> arity t
    TyParen t -> arity t
    TyKind t k -> arity t
    TyFun t1 t2 -> (arity' t2) 
    _ -> 0 --trace (show ty) 0
   where 
     arity' ty = 
       case ty of
         TyFun t1 t2 -> 1 + (arity' t2) 
         _ -> 1
-- List of types in a function type
typs_of_fun ty =     
  case ty of
    TyForall _ _ t -> typs_of_fun t
    TyParen t -> typs_of_fun t
    TyKind t k -> typs_of_fun t
    TyFun t1 t2 -> t1:(typs_of_fun' t2) 
    _ -> [ty]
   where 
     typs_of_fun' ty =
       case ty of 
         TyFun t1 t2 -> t1:(typs_of_fun' t2)
         _ -> [ty] 
         
{-
-- Collect datatype name and types.
get_datatypes dec dmap = 
  case dec of 
     DataDecl loc dataOrNew context name tyVarBnds qualConDecls decls -> 
       Map.insert name typ dmap
       where
         typ = foldr build_typ (TyCon (UnQual name)) tyVarBnds 
         build_typ tyvar ty = TyApp ty quickSpecType
     _ -> dmap  
 -}    

-- Collect function names and types from typesignatures.      
get_funTyps dec (typSet, constMap) =
  case dec of
    TypeSig _ names typ -> (Set.union typSet (Set.fromList (typs_of_fun mtyp)), 
                            Map.insert (head names) (arity typ, mtyp) constMap) 
      where
        mtyp = monom typ
    _ -> (typSet,constMap)
    
    
-- Collect datatype constructors names and types.  
get_constructors dec cmap =     
  case dec of 
     DataDecl loc dataOrNew context name tyVarBnds qualConDecls decls -> 
       foldr (get_constructor (typ_of_datatype name tyVarBnds)) cmap qualConDecls
     _ -> cmap 
     
get_constructor result_typ (QualConDecl loc tyVarBinds ctxt conDecl) cmap = 
  case conDecl of
    ConDecl name argtyps -> Map.insert name (length argtyps, mk_funtyp argtyps result_typ) cmap
    -- Not 100% sure the below is right for infix function types...
    InfixConDecl typ1 name typ2 -> Map.insert name (2, mk_funtyp [typ1,typ2] result_typ) cmap
    RecDecl name fields -> cmap -- Currently no support for records!  

typ_of_datatype name tyVarBnds = 
  foldr (\tyvar -> \ty -> 
          case tyvar of
            UnkindedVar tyvarnm -> TyApp ty quickSpecType --(TyVar tyvarnm) 
            KindedVar tyvarnm _ -> TyApp ty quickSpecType) --(TyVar tyvarnm))
  (TyCon (UnQual name)) tyVarBnds


mk_funtyp argtyps resulttyp = 
  case argtyps of 
    [] -> monom resulttyp
    _ -> foldr funtype_aux (monom resulttyp) argtyps
    where
      funtype_aux argty typ = 
        case argty of 
          UnBangedTy arg -> TyFun (monom arg) typ
          _ -> error "mk_funtyp: No support for Bangtypes right now."             
          
          
--------------------------------------------------------------------------------------             
          
-- Pre-processes a Haskell file, which we assume was produced by Isabelle, 
--- adding HipSpec/QuickSpec specific things that are required.
main = do
  [mode, file, fileout] <- getArgs
  sin <- readFile file  
  writeFile fileout (prettyPrint 
                     (process mode
                      (parseModuleWithMode 
                       defaultParseMode{extensions=[EnableExtension(TypeOperators),
                                                    EnableExtension(ExplicitForAll)]} sin)))

