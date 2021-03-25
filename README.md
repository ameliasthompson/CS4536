# CS 4536: Programming Languages

CS 4536 was a course on the structure of programming languages and interpreters. The homework consisted of writing Racket code to interptet tokens generated with the parser provided by Professor Dougherty in order to implement a basic functional programming language. The language allowed basic arithmatic, logic, state, definition of both first class functions, and invoking functions.

## Assignment Breakdown

Each homework folder (save for the first) contains both a compeleted assignment and the starter file provided by Professor Dougherty. This is a breakdown of what each homework assignment covers:

### Homework 1

The first assignment is a brief overview of the Racket language for those who were not familiar with Racket at the start of the course.

### Homework 2

The second assignment covered the initial stages of the interpreter: implementation of interpretting the tokens for basic arithmatic, number literals, if0, and both the definition and invocation of first class functions. An environment existed only for first class function definition and binding.

### Homework 3

The third assignment covered the implementation of mutability and state. The environment consisted of both variables and first class functions where only the most recent definition of each binding was used.

### Homework 4

The fourth assignment dialed back some of the requirements of the previous assignments and focused on the implementation of typing and type checking.

## Running the Projects

Each assignment (save for the first) can be run in a Racket interpretter. The end of each file contains a series of tests that test the definitions at the head of each file. Additionally, the definitions may be used in the console after running the file without requiring modification of the assignment file.