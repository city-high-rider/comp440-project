module All

import Elem

%default total

public export
data All : (pred : a -> Type) -> List a -> Type where
  VacuouslyTrue : All pred []
  (::) : {x: a} -> pred x -> All pred xs -> All pred (x :: xs)

public export total
propImplies : {prem1, prem2 : a -> Type} -> ((e : a) -> prem1 e -> prem2 e) -> All prem1 es -> All prem2 es
propImplies f VacuouslyTrue = VacuouslyTrue
propImplies f (cur :: rest) = f _ cur :: propImplies f rest

public export total
extractPrf : x `Elem` xs -> All prop xs -> prop x
extractPrf Here (y :: _) = y
extractPrf (KeepLooking y) (_ :: w) = extractPrf y w

public export total
allAOrBMeansAllAOrOneB : {a : Type} -> {es : List a} -> {propA, propB : a -> Type} -> All (\e => Either (propA e) (propB e)) es -> Either (All propA es) (e ** (propB e, e `Elem` es))
allAOrBMeansAllAOrOneB VacuouslyTrue = Left VacuouslyTrue
allAOrBMeansAllAOrOneB ((::) {x=thisElem} aOrB rest) =
  case aOrB of
       (Left isA) =>
          case allAOrBMeansAllAOrOneB rest of
               (Left restAllA) => Left (isA :: restAllA)
               (Right (restOneB ** (prfB, prfElemRest))) => Right (restOneB ** (prfB, KeepLooking prfElemRest))
       (Right isB) => Right (thisElem ** (isB, Here))

public export total
falsePropEmptyList : All (\e => Void) es -> es = []
falsePropEmptyList VacuouslyTrue = Refl
falsePropEmptyList (someVoid :: _) = absurd someVoid

