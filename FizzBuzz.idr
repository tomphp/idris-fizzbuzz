data IsDivisibleBy : (divisor : Nat) -> (dividend : Nat) -> Type where
  MkIsDivisibleBy : (dividend : Nat)
         -> (divisor : Nat)
         -> (prf : modNat dividend divisor = 0)
         -> IsDivisibleBy divisor dividend

isNotAMultiple : (contra : modNat dividend divisor = 0 -> Void) -> IsDivisibleBy divisor dividend -> Void
isNotAMultiple contra (MkIsDivisibleBy dividend divisor prf) = contra prf

isDivisibleBy : (divisor : Nat) -> (dividend : Nat) -> Dec (IsDivisibleBy divisor dividend)
isDivisibleBy divisor dividend
  = case decEq (modNat dividend divisor) Z of
         Yes prf => Yes (MkIsDivisibleBy dividend divisor prf)
         No contra => No (isNotAMultiple contra)

IsFizz : Nat -> Type
IsFizz = IsDivisibleBy 3

IsBuzz : Nat -> Type
IsBuzz = IsDivisibleBy 5

data FizzBuzzT : (k : Nat) -> Type where
  Fizz : (k : Nat) -> IsFizz k -> Not (IsBuzz k) -> FizzBuzzT k
  Buzz : (k : Nat) -> Not (IsFizz k) -> IsBuzz k -> FizzBuzzT k
  FizzBuzz : (k : Nat) -> IsFizz k -> IsBuzz k -> FizzBuzzT k
  Number : (k : Nat) -> Not (IsFizz k) -> Not (IsBuzz k) -> FizzBuzzT k

isFizz : (k : Nat) -> Dec (IsFizz k)
isFizz = isDivisibleBy 3

isBuzz : (k : Nat) -> Dec (IsBuzz k)
isBuzz = isDivisibleBy 5

fizzBuzz : (k : Nat) -> FizzBuzzT k
fizzBuzz k
  = case isFizz k of
         Yes isFizzProof
           => case isBuzz k of
                   Yes isBuzzProof   => FizzBuzz k isFizzProof isBuzzProof
                   No isNotBuzzProof => Fizz k isFizzProof isNotBuzzProof
         No isNotFizzProof
           => case isBuzz k of
                   Yes isBuzzProof   => Buzz k isNotFizzProof isBuzzProof
                   No isNotBuzzProof => Number k isNotFizzProof isNotBuzzProof

showFizzBuzz : Nat -> String
showFizzBuzz k = case fizzBuzz k of
                  Fizz k _ _     => "fizz"
                  Buzz k _ _     => "buzz"
                  FizzBuzz k _ _ => "fizzbuzz"
                  Number k _ _   => show k
