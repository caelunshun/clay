# Clay

For CS 6110: To run the demo shown in the course...

- The current working directory must be the project root.
- `rustc` and `cargo` must be installed (see https://rustup.rs/)
- Many tests are currently broken since not all constructs are lowered. However, the following tests work and demonstrate some interesting aspects of the borrow-checker...
  - `cargo run -p fir-frontend crates/frontend/samples/test28.fir`
    - Runs the entire compilation process up to borrow-checking, reporting a lifetime error because `x` is discarded while `y`, a reference to it, is still live.
  - `cargo run -p fir-frontend crates/frontend/samples/test30.fir`
    - Demos the way in which type-checking can affect lifetimes non-trivially. There are false negatives for "local used before initialized" because I haven't lowered function arguments yet.
