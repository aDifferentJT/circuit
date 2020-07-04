module AuxProofs

%default total

%access public export

rewriteEither : (a = a') -> (b = b') -> Either a b = Either a' b'
rewriteEither Refl Refl = Refl

rewritePair : (a = a') -> (b = b') -> Pair a b = Pair a' b'
rewritePair Refl Refl = Refl

rewriteIsJust : (x = y) -> IsJust x -> IsJust y
rewriteIsJust {x = Nothing} _ _ impossible
rewriteIsJust {x = Just x} {y = Nothing} Refl _ impossible
rewriteIsJust {x = Just x} {y = Just y} _ _ = ItIsJust

