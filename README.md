# Beaver: a solver for halting problem of Brainfuck programs

According to a well-known theorem about the [halting problem](https://en.wikipedia.org/wiki/Halting_problem), there are algorithms, for which we can't prove that they run forever, or stop. The smallest Turing machines, for which it is unknown whether they stop or not have dimentions are 5-state-2-symbol, 3-state-3-symbol and 2-state-4-symbol. What if instead of the smallest Turing machines we are looking for the shortest [Brainfuck](https://en.wikipedia.org/wiki/Brainfuck) programs?

This project tries to achieve the following goals:

* Find the shortest Brainfuck program, for which we can't tell whether it stops or not.
* Find the Busy Beaver Brainfuck programs for various lengths: the programs that take the most steps or touch the most cells, and then ultimatelty stop.

See [results](#results) below. Spoiler: we ran all programs up to length 16 and solved halting problem for all programs up to length 12.

## Usage

    beaver 7

Iterate through all Brainfuck programs of length 7 and try to either trace them until they stop, or prove that they will run forever. The program will print some statistics, [busy beavers](https://en.wikipedia.org/wiki/Busy_beaver) (the longest running stopping program, and the program touching the most cells on the tape), and all the programs for which it couldn't find the proof that they are not stopping, and couldn't run until stopping.

    beaver '+>[[]<]'

Try to prove that a given program runs forever, and print the proof as a series of invariants after each step of the program (this particular program doesn't work in this version though).

## Method

First we run the program for up to 5000 steps to see whether it will stop normally or due to an overflow. If it hasn't happened, we try to prove that the program will run forever (or will eventually overflow — the proof doesn't distinguish between those cases).

To prove that the program runs forever we construct the series of predicates about the tape, that act as invariants after each step of the program. The predicates are composed using the following primitives:

* `True` — true for any tape
* `False` — false for any tape
* `ZerosFrom(offset)` — all cells starting from the `offset` are zero. For instance if the currently selected cell has address 3, the predicate `ZerosFrom(-1)` means that all the cells from 2 on are filled with zeros. The invariant before execution of the first step is `ZerosFrom(0)`: all tape is filled with 0s.
* `Equals(offset, value)` — the value at the `offset` is `value`.
* `GreaterThan(offset, value)` — the value at the `offset` is greater than `value`.
* `All(pred1, pred2, ...)` — all of the predicates `pred1`, `pred2` and so on hold.
* `Any(pred1, pred2, ...)` — any of the predicates `pred1`, `pred2` and so on holds.

We start at step 0, and trace the program, modifying the current invariant according to the performed operations. When we meet a `]`, then:
- if we can infer from the current invariant that `Equals(0, 0)`, then we go forward,
- if we can infer that `GreaterThan(0, 0)`, then we loop to the beginning of the loop,
- and if we can't infer either, we fork the execution, and continue tracing from two points with updated predicates: the invariant in the beginning of loop is `All(pred, GreaterThan(0, 0))`, the invariant after the loop is `All(pred, Equals(0, 0))`, where `pred` is the current invariant.

If we get to the point where we've already been, and that thus has an invariant `i1`, and our current invariant is `i2`, we check whether `i2 ⇒ i1`. If yes, then we stop the current branch, since we've proven the invariant for it. If no, then we replace the invariant with a new invarian `i3`, which follows both from `i1` and from `i2`, and continue tracing through this step, updating the following invariants. Finding a good `i3` is the hard part. We take `i1 | i2` and then weaken it a bit.

If we ever reach the end of the program in any branch of execution, the we've failed to prove that it runs forever.

## Dialect of Brainfuck

The Brainfuck programs that we examine do not have any input or output.

To exclude some uninteresting long-running programs we use a pretty restrictive version of Brainfuck:

* Any seeks to the left of the cell zero result in overflow and program halting.
* The values in the cells are from 0 to 255.
* Increment of 255 and decrement of 0 result in overflow and program halting.

The prover assumes that all the operations are successful, so the proof of non-stopping actually means that the program either runs forever, or stops due to an overflow. 

## Results

Number of programs per length:

| Length | Total           | Finishing      | Infinite or overflow | Overflow        | Unknown   |
| ------ | --------------- | -------------- | -------------------- | --------------- | --------- |
| 1      | 4               | 2              |                      | 2               |           |
| 2      | 17              | 7              |                      | 10              |           |
| 3      | 76              | 24             | 1                    | 51              |           |
| 4      | 354             | 98             | 6                    | 250             |           |
| 5      | 1'704           | 413            | 39                   | 1'252           |           |
| 6      | 8'421           | 1'871          | 216                  | 6'334           |           |
| 7      | 42'508          | 8'740          | 1'486                | 32'282          |           |
| 8      | 218'318         | 42'347         | 6'574                | 169'397         |           |
| 9      | 1'137'400       | 209'880        | 35'890               | 891'630         |           |
| 10     | 5'996'938       | 1'063'012      | 195'327              | 4'738'599       |           |
| 11     | 31'940'792      | 5'471'231      | 1'066'548            | 25'403'013      |           |
| 12     | 171'605'956     | 28'565'478     | 7'261'980            | 135'778'498     |           |
| 13     | 928'931'280     | 150'873'711    | 39'835'924           | 738'221'643     | 2         |
| 14     | 5'061'593'709   | 804'952'161    | 219'235'068          | 4'037'406'458   | 22        |
| 15     | 27'739'833'228  | 4'331'432'233  | 1'210'670'173        | 22'197'730'421  | 401       |
| 16     | 152'809'506'582 | 23'482'328'064 | 6'708'160'321        | 122'619'013'779 | 4418      |

Beasy beavers:

| Length | Longest running        | Touching most cells   |
| ------ | ---------------------- | --------------------- |
| 1      | `+` 1                  | `>` 2                 |
| 2      | `++` 2                 | `>>` 3                |
| 3      | `+++` 3                | `>>>` 4               |
| 4      | `++++` 4               | `>>>>` 5              |
| 5      | `++[-]` 7              | `>>>>>` 6             |
| 6      | `+++[-]` 10            | `>>>>>>` 7            |
| 7      | `++++[-]` 13           | `>>>>>>>` 8           |
| 8      | `+++++[-]` 16          | `>>>>>>>>` 9          |
| 9      | `++++[+--]` 21         | `>>>>>>>>>` 10        |
| 10     | `+++++[+--]` 26        | `>>>>>>>>>>` 11       |
| 11     | `++++++[+--]` 31       | `>>>>>>>>>>>` 12      |
| 12     | `++++++[->+<]` 37      | `>>>>>>>>>>>>` 13     |
| 13     | `>++++[-[>]+<]` 53     | `>>>>>>>>>>>>>` 14    |
| 14     | `>+[>+++[-<]>>]` 110   | `>>>>>>>>>>>>>>` 15   |
| 15     | `>+[>++++[-<]>>]` 153  | `>>>>>>>>>>>>>>>` 16  |
| 16     | `+[->++++++[-<]>]` 537 | `>>>>>>>>>>>>>>>>` 17 |

Here are all the programs of length 13-14 for which `beaver` can't automatically prove that they aren't stopping:
    
    +++[-[+[>]]+<]
    ++[-[++[>]]+<]
    ++[-[+>[>]]+<]
    ++[-[+[>]]+<]
    ++[>>[>]+[<]<]
    +[>>[>]++[<]<]
    +[>>[>]+<[<]<]
    +[>>[>]+[<]<]
    >++[-[+[>]]+<]
    +[[>>]+>+[<]<]
    >+[>+<+[-<]>>]
    >+[>+<<[-<]>>]
    >+[+>++[-<]>>]
    >+[+>+<[-<]>>]
    >+[>>[>]+[<]<]
    >+[+[>]+[<]>-]