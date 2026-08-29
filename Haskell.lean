#check List
#check List.map
#check List.filter
#check List.foldl
#check List.foldr
#check List.head
#check List.tail

def mySum(xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => y + mySum ys

#check mySum
#eval mySum [1, 2, 3, 4, 5]
#reduce mySum [1, 2, 3, 4, 5]

def myLength(xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => 1 + myLength ys

#check myLength
#eval myLength [1, 2, 3, 4, 5]
#reduce myLength [1, 2, 3, 4, 5]

def onlyEven(xs : List Nat) : List Nat :=
  match xs with
  | [] => []
  | y :: ys => if y % 2 == 0 then y :: onlyEven ys else onlyEven ys

#check onlyEven
#eval onlyEven [1, 2, 3, 4, 5]
#reduce onlyEven [1, 2, 3, 4, 5]
