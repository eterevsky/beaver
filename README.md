# Beaver: a solver for halting problem of Brainfuck programs

<https://en.wikipedia.org/wiki/Halting_problem>

<https://en.wikipedia.org/wiki/Brainfuck>

## Usage:

    beaver 7

Iterate through all Brainfuck programs of length 7 and try to either trace them until they stop, or prove that they will run forever. The program will print some statistics, [busy beavers}(https://en.wikipedia.org/wiki/Busy_beaver) (the longest running stopping program, and the program touching the most cells on the tape), and all the programs for which it couldn't find the prove that they are not stopping, and couldn't trace until stopping.

    beaver '+>[[]<]'

Try to prove that a given program runs forever, and print the proof as a series of invariants after each step of the program (this particular program doesn't work in this version though).

## How we do it

We are trying to construct the series of predicates about the tape, that act as invariants after each step of the program. The predicates are composed using the following primitives:

* `True` – true for any tape
* `False` — false for any tape
* `ZerosFrom(offset)` – all cells starting from the `offset` are zero. For instance if the currently selected cell has address 3, the predicate `ZerosFrom(-1)` means that all the cells from 2 on are filled with zeros. The invariant before execution of the first step is `ZerosFrom(0)`: all tape is filled with 0s.
* `Equals(offset, value)` – the value at the `offset` is `value`.
* `GreaterThan(offset, value)` – the value at the `offset` is greater than `value`.
* `All(pred1, pred2, ...)` – all of the predicates `pred1`, `pred2` and so on hold.
* `Any(pred1, pred2, ...)` – any of the predicates `pred1`, `pred2` and so on holds.

We start at step 0, and trace the program, modifying the current invariant according to the performed operations. When we meet a `]`, then:
- if we can infer from the current invariant that `Equals(0, 0)`, then we go forward,
- if we can infer that `GreaterThan(0, 0)`, then we loop to the beginning of the loop,
- and if we can't infer either, we fork the execution, and continue tracing from two points with updated predicates: the invariant in the beginning of loop is `All(pred, GreaterThan(0, 0))`, the invariant after the loop is `All(pred, Equals(0, 0))`, where `pred` is the current invariant.

If we get to the point where we've already been, and that thus has an invariant `i1`, and our current invariant is `i2`, we check whether `i2 => i1`. If yes, then we stop the current branch, since we've proven the invariant for it. If no, then we replace the invariant with a new invarian `i3`, which follows both from `i1` and from `i2`, and continue tracing through this step, updating the following invariants.

If we ever reach the end of the program in any branch of execution, we've failed to prove that it runs forever.

## Dialect of Brainfuck

The Brainfuck programs that we examine do not have any input or output.

To exclude some uninteresting long-running programs we use a pretty restrictive version of Brainfuck:

* Any seeks to the left of the cell zero result in overflow and program halting.
* The values in the cells are from 0 to 255.
* Increment of 255 and decrement of 0 result in overflow and program halting.

The prover assumes that all the operations are successful, so the proof of non-stopping actually means that the program either runs forever, or stops due to an overflow. 

## Results

Number of programs per length:

| Length | Total       | Finishing  | Infinite   | Overflow    | Unknown   |
| ------ | ----------- | ---------- | ---------- | ----------- | --------- |
| 1      | 4           | 2          |            | 2           |           |
| 2      | 17          | 7          |            | 10          |           |
| 3      | 76          | 21         | 1          | 54          |           |
| 4      | 354         | 79         | 7          | 268         |           |
| 5      | 1'704       | 278        | 49         | 1'377       |           |
| 6      | 8'421       | 1'099      | 289        | 7'033       |           |
| 7      | 42'508      | 4'218      | 1'683      | 36'607      |           |
| 8      | 218'318     | 17'293     | 9'430      | 191'595     |           |
| 9      | 1'137'400   | 69'993     | 52'487     | 1'014'914   | 6         |
| 10     | 5'996'938   | 295'042    | 289'226    | 5'412'596   | 74        |
| 11     | 31'940'792  | 1'237'258  | 1'590'890  | 29'111'808  | 836       |
| 12     | 171'605'956 | 5'329'766  | 8'642'674  | 157'395'298 | 238'218*  |
| 13     | 928'931'280 | 22'921'438 | 47'341'020 | 857'130'730 | 1'538'092* |

^* Haven't run the latest version.

Beasy beavers:

| Length | Longest running    | Touching most cells |
| ------ | ------------------ | ------------------- |
| 1      | `+` 1              | `>` 2               |
| 2      | `++` 2             | `>>` 3              |
| 3      | `+++` 3            | `>>>` 4             |
| 4      | `++++` 4           | `>>>>` 5            |
| 5      | `++[-]` 8          | `>>>>>` 6           |
| 6      | `+++[-]` 12        | `>>>>>>` 7          |
| 7      | `++++[-]` 16       | `>>>>>>>` 8         |
| 8      | `+++++[-]` 20      | `>>>>>>>>` 9        |
| 9      | `++++[-+-]` 24     | `>>>>>>>>>` 10      |
| 10     | `+++++[-+-]` 30    | `>>>>>>>>>>` 11     |
| 11     | `[>+++[-<]>]` 41   | `>>>>>>>>>>>` 12    |
| 12     | `[>++++[-<]>]` 60  | `>>>>>>>>>>>>` 13   |
| 13     | `[>+++++[-<]>]` 81 | `>>>>>>>>>>>>>` 14  |

Some of the simplest programs for which `beaver` can't automatically prove they aren't stopping:
    
    +>>[<[]+]
    +>>[[]<<]
    >+[>[<]>]
    >+>[[<]>]
    >+>[<]+[]
    >+>[<]>[]
