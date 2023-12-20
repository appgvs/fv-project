theory Export
    imports
      CvRDT
      USet
      PNSet
      Log
      IntegerVector
      GCounter
      (* "~~/src/HOL/Library/Code_Target_Numeral" *)
begin

export_code
  "USet" "USet.initial" "USet.add" "USet.query" "USet.merge"
  "PNSet" "PNSet.initial" "PNSet.add" "PNSet.remove" "PNSet.query" "PNSet.merge"
  "Log" "Log.initial" "Log.update" "Log.elements" "Log.union"
  "IntegerVector.query" "IntegerVector.merge" "IntegerVector.update"
  "GCounter" "GCounter.initial_counter" "GCounter.query" "GCounter.merge" "GCounter.increment"
in Scala

end