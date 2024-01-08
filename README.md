# Formally Verified Conflict-Free Replicated Data Types

**Class**: CS-550, Formal Verification [(EPFL Website)](https://edu.epfl.ch/coursebook/en/formal-verification-CS-550)

## Team

| Name | Email |
|---|---|
| Alexandre Piveteau | alexandre.piveteau@epfl.ch |
| Patrick Gilliard | patrick.gilliard@epfl.ch |
| Victor Schneuwly | victor.schneuwly@epfl.ch |

## Setup

This project uses the Isabelle/HOL proof assistant. The project can be run
as follows:

```bash
isabelle build -D . CRDT

# Generates the browser info
isabelle build -D . -o browser_info -v
```

## Structure

Here's a short rundown of the files from this repository:

+ [ROOT](ROOT): the Isabelle/HOL root file.
+ [CvRDT.thy](CvRDT.thy): the CvRDT locale, and its lemmas.
+ [Export.thy](Export.thy): Scala export for the CvRDTs.
+ Set-based CvRDTs theories:
  - [USet](USet.thy);
  - [Log](Log.thy); and
  - [PNSet](PNSet.thy).
+ Vector-based CvRDTs theories:
  - [IntegerVector](IntegerVector.thy); and
  - [GCounter](GCounter.thy).
+ Work-in-progress theories are available in the [wip](wip) folder.
