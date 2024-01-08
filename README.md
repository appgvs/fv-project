# Formally Verified Conflict-Free Replicated Data Types

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
