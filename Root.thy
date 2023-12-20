theory Root
    imports CvRDT USet PNSet
begin

export_code
  "USet" "USet.initial" "USet.add" "USet.elements"
  "PNSet" "PNSet.initial" "PNSet.add" "PNSet.remove" "PNSet.query"
in Scala

end