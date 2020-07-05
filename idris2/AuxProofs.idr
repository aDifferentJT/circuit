module AuxProofs

%default total

public export
rewriteEither : (a = a') -> (b = b') -> Either a b = Either a' b'
rewriteEither Refl Refl = Refl

public export
rewritePair : (a = a') -> (b = b') -> Pair a b = Pair a' b'
rewritePair Refl Refl = Refl

