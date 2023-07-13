# Dafny Consul

From the AWS [Cedar Spec](https://github.com/cedar-policy/cedar-spec/tree/main). The Cedar spec repo lays out a great example for the setup of fuzz testing and more advanced theorems as well. I highly recommend taking a look and reading the [blog post](https://www.amazon.science/blog/how-we-built-cedar-with-automated-reasoning-and-differential-testing)!

Encodes a basic model of consul intentions and uses the dafny verifier to prove our assumptions about how the model works. Future work includes fuzz testing the model and production implementation to verify that assertions proved in dafny hold for the production version.

## Installation

* [dafny installation](https://github.com/dafny-lang/dafny/wiki/INSTALL)
    * Though I recommend installing `dafny` and the appropriate `dotnet core` from `brew` if on mac.
* [vscode plugin](https://marketplace.visualstudio.com/items?itemName=dafny-lang.ide-vscode)

## Verifying Consul

The dafny verifier is used to verify the functional correctness of programs. Dafny allows us to write assertions for many part of the program. 
We can add assertion to verify the state meets our assumptions at various points in the code, pre- and postconditions to ensure that the parameters
entering and being returned from methods are within expected bounds, as well as lemmas that state properties which should hold at all times. 
