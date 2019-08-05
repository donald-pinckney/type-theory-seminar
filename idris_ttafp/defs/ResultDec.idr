module defs.ResultDec

public export
data ResultDec : Type -> Type where
    Ok : prop -> ResultDec prop
    Error : String -> Not prop -> ResultDec prop

export
decToResultDec : Dec t -> ResultDec t
decToResultDec (Yes prf) = Ok prf
decToResultDec (No contra) = Error "UNKNOWN ERROR" contra
