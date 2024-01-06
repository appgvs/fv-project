# CvRDTs exported from Isabelle/HOL to Scala 3
Usage examples of the CvRDTs exported from Isabelle/HOL to Scala 3.

## Usage
### IntegerVector
A small example using the `IntegerVector` can be found in the [`Main.scala`](src/main/scala/Main.scala) file.
It can be ran using the following command:
```bash
sbt run
```

### GCounter
A test suite for the `GCounter` can be found in the [`TestGCounter.scala`](src/test/scala/TestGCounter.scala) file.
It tests basic operations on the `GCounter` as well as an example showing that, given a trace of increments and merges, the final state is the same regardless of the order of the operations.
The tests can be ran using the following command:
```bash
sbt test
```
