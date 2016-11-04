(* $Id: bigint.ml,v 1.5 2014-11-11 15:06:24-08 - - $ *)

open Printf

module Bigint = struct

    type sign     = Pos | Neg
    type bigint   = Bigint of sign * int list
    let  radix    = 10
    let  radixlen =  1

    let car       = List.hd
    let cdr       = List.tl
    let map       = List.map
    let reverse   = List.rev
    let length    = List.length
    let strcat    = String.concat
    let strlen    = String.length
    let strsub    = String.sub
    let zero      = Bigint (Pos, [])

    
    (*Get rid of the leading zeros for a list*)
    let ridzeros list =
        let rec ridzeros' list' = match list' with
            | []      -> []
            | [0]     -> []
            |car::cdr -> 
                let cdr' = ridzeros' cdr
                in match car, cdr' with
                    | 0, []     -> []
                    | car, cdr' -> car::cdr'
        in ridzeros' list


    let charlist_of_string str = 
        let last = strlen str - 1
        in  let rec charlist pos result =
            if pos < 0
            then result
            else charlist (pos - 1) (str.[pos] :: result)
        in  charlist last []


    let bigint_of_string str =
        let len = strlen str
        in  let to_intlist first =
                let substr = strsub str first (len - first) in
                let digit char = int_of_char char - int_of_char '0' in
                map digit (reverse (charlist_of_string substr))
            in  if   len = 0
                then zero
                else if   str.[0] = '_'
                     then Bigint (Neg, to_intlist 1)
                     else Bigint (Pos, to_intlist 0)
    
    

    let string_of_bigint (Bigint (sign, value)) =
        match value with
        | []    -> "0"
        | value -> let reversed = reverse value
                   in  strcat ""
                       ((if sign = Pos then "" else "-") ::
                        (map string_of_int reversed))


  (*--------------------------------------------------------------------------------------------------------------*)
  (*Tail-Recursive Helper Functions-------------------------------------------------------------------------------*)
  (*--------------------------------------------------------------------------------------------------------------*)


    (*Helper function for compare*)
    let rec compare' list1 list2 = match(list1, list2) with
        | [],[]                  -> 0
        | list1, []              -> 1
        | [], list2              -> -1
        | car1::cdr1, car2::cdr2 ->
            let value = compare' cdr1 cdr2
            in if value = 0 && car1 != car2
               then (if car1 > car2
                     then 1
                     else (if car1 < car2
                           then -1
                           else 0))
               else value 


    (*Helper function for add*)
    let rec add' list1 list2 carry = match (list1, list2, carry) with
        | list1, [], 0       -> list1
        | [], list2, 0       -> list2
        | list1, [], carry   -> add' list1 [carry] 0
        | [], list2, carry   -> add' [carry] list2 0
        | car1::cdr1, car2::cdr2, carry ->
          let sum = car1 + car2 + carry
          in  sum mod radix :: add' cdr1 cdr2 (sum / radix)

    
    (*Doubles a number*)
    let double number =
        add' number number 0


    (*Helper function for sub*)
    let rec sub' list1 list2 borrow = match (list1, list2, borrow) with
        | list1, [], 0                   -> list1
        | [], list2, 0                   -> failwith "subtraction: list2 is larger than list1"
        | car1::cdr1, [], borrow          -> 
          if car1 = 0
          then 9 :: (sub' cdr1 [] 1)
          else let difference = car1 - borrow*1
              in difference:: (sub' cdr1 [] 0)
        | [], list2, borrow              -> failwith "subtraction: list2 is larger than list1"

        |car1::cdr1, car2::cdr2, borrow  ->
         if car2 > (car1 - borrow*1)
         then let difference = ((car1 + 10) - borrow*1) - car2
             in difference :: (sub' cdr1 cdr2 1)
         else let difference = (car1 - borrow*1) - car2
             in difference :: (sub' cdr1 cdr2 0)


    (*Helper function for mul*)
    let rec mul' (multiplier, powerof2, multiplicand) =
        if (compare' powerof2 multiplier) = 1
        then multiplier, []
        else let remainder, product =
            mul' (multiplier, double powerof2, double multiplicand)
        in if (compare' powerof2 remainder) = 1
           then remainder, product
           else (ridzeros(sub' remainder powerof2 0)), (add' product multiplicand 0) 


    (*Helper function for divrem*)
    let rec divrem' (dividend, powerof2, divisor) =
        if (compare' divisor dividend) = 1
        then [0], dividend
        else let quotient, remainder =
            divrem' (dividend, double powerof2, double divisor)
            in if(compare' divisor remainder) = 1
                then quotient, remainder
                else (add' quotient powerof2 0), (ridzeros(sub' remainder divisor 0))


  (*--------------------------------------------------------------------------------------------------------------*)
  (*Main arithmetic Functions-------------------------------------------------------------------------------------*)
  (*--------------------------------------------------------------------------------------------------------------*)


    (*Returns -1 if the first Bigint is less than the second
     *or 1 of the first Bigint is larger than the second*)
    let compare (Bigint (sign1, value1)) (Bigint (sign2, value2)) =
        if sign1 = sign2
        then compare' value1 value2
        else if sign1 = Neg
             then -1
             else 1


    (*Adds two lists*)
    let add (Bigint (sign1, value1)) (Bigint (sign2, value2)) =
        if sign1 = sign2
        then Bigint (sign1, add' value1 value2 0)
        else if (compare' value1 value2) = 1
             then Bigint (sign1, ridzeros(sub' value1 value2 0))
             else Bigint (sign2, ridzeros(sub' value2 value1 0))       

   
   (*Subtracts two lists*)
    let sub (Bigint (sign1, value1)) (Bigint (sign2, value2)) =
        if sign1 = sign2
        then (if (compare' value2 value1) = 1
              then Bigint (Neg, ridzeros(sub' value2 value1 0))
              else Bigint (Pos, ridzeros(sub' value1 value2 0)))

        else (if (compare' value1 value2) = 1
              then Bigint (sign2, add' value1 value2 0)
              else Bigint (sign1, add' value2 value1 0))


    (*Multiplies two lists*)
    let mul (Bigint (sign1, value1)) (Bigint (sign2, value2)) =
        let _, product =
            mul' (value1, [1], value2) in
                if sign1 = sign2
                then Bigint (Pos, product)
                else Bigint (Neg, product) 

    
    (*Returns a tuple containg the quotient and remainder of two lists*)
    let divrem ((Bigint (sign1, value1)), (Bigint (sign2, value2))) =
        let quotient, remainder = divrem' (value1, [1], value2)
        in if sign1 = sign2
        then Bigint (Pos, quotient), Bigint (Pos,remainder)
        else Bigint (Neg, quotient), Bigint (Pos, remainder)


    (*Returns the quotient of two numbers*)    
    let div (Bigint (sign1, value1)) (Bigint (sign2, value2)) =
        let quotient, _ = divrem ((Bigint (sign1, value1)),
                                   (Bigint (sign2, value2)))
        in quotient


    (*Returns the remainder of two numbers*)
    let rem (Bigint (sign1, value1)) (Bigint (sign2, value2)) =
        let _, remainder = divrem ((Bigint (sign1, value1)),
                                    (Bigint (sign2, value2)))
      in remainder


    (*--------------------------------------------------------------------------------------------------------------*)
    (*Functions for exponent----------------------------------------------------------------------------------------*) 
    (*--------------------------------------------------------------------------------------------------------------*) 
    

    (*Checks if a Bigint is even*)
    let iseven (Bigint (sign1, value1)) =
        let _, remainder = rem (Bigint (sign1, value1)),
                                (Bigint (Pos, [2]))

            in (compare remainder zero) = 0


    (*Recursive helper function for pow*)
    let rec pow' ((Bigint (sign1, base)), (Bigint (sign2, exponent)), (Bigint (sign3, result))) =
        match (Bigint (sign2, exponent)) with
            | (Bigint (sign2, exponent)) when (compare (Bigint (sign2, exponent)) zero) = 0  ->
                   (Bigint (sign3, result))

            | (Bigint (sign2, exponent)) when iseven (Bigint (sign2, exponent))              ->
                  pow' (mul (Bigint (sign1, base)) (Bigint (sign1, base)),
                        (div (Bigint (sign2, exponent)) (Bigint (sign1, base))),
                        (Bigint (sign3, result))) 

            | (Bigint (sign2, exponent))                                                     ->
                  pow' ((Bigint (sign1, base)),
                        (sub (Bigint (sign2, exponent)) (Bigint (Pos, [1]))),
                        (mul (Bigint (sign1, base)) (Bigint (sign3, result))))
    
    
    (*Raise first number to power of second*)
    let pow (Bigint (sign1, value1)) (Bigint (sign2, value2)) =
        if (compare (Bigint (sign2, value2)) zero) = -1
            then pow' ((div (Bigint (Pos, [1])) (Bigint (sign1, value1))),
                       (Bigint (sign2, value2)), (Bigint (Pos, [1])))
            else pow' ((Bigint (sign1, value1)), (Bigint (sign2, value2)),
                       (Bigint (Pos, [1])))



end
























