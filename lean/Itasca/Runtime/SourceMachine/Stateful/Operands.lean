import Itasca.Runtime.SourceMachine.Safety
namespace Itasca.Runtime.SourceMachine.Stateful

def popThree (values : List val) : Option (List val × val × val × val) :=
  match pop values with
  | none => none
  | some (first,c) => match pop first with
    | none => none
    | some (second,b) => match pop second with
      | none => none
      | some (front,a) => some (front,a,b,c)

@[simp] theorem pop_three_append (front : List val) (a b c : val) :
    popThree (front ++ [a,b,c]) = some (front,a,b,c) := by
  have split : front ++ [a,b,c] = ((front ++ [a]) ++ [b]) ++ [c] := by simp [List.append_assoc]
  simp only [popThree,split,pop_append]
end Itasca.Runtime.SourceMachine.Stateful
