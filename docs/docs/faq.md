

# ？FAQ 


## Why is it named greed? 

We all know why people are so interested in finding vulnerabilities in smart contracts..., right? ;) 

## How should "greed" be stylized? 

Simple: greed, no upper case.

## Why didn't you just implement everything on top of angr?

While implementing everything on top of angr could have been an option, some of the fundamentals of EVM analysis are quite different compared to classic binaries (ARM, x86, AMD64, etc...).
We found out that building a system from scratch was actually easier rather than implementing what we needed in a complex software like angr.
Moreover, we wanted to re-use the high-quality analysis (e.g., CFG) and IR offered by Gigahorse, thus, starting from square one was an easier option rather than fighting with the angr codebase.


## Does greed support non-EVM contracts?

greed automatically supports whatever is supported by Gigahorse. Currently, Gigahorse does not support any non-EVM binary, thus, greed does not.

## Can greed work with contracts source code?

Yes. Just compile the contract, decompile it with Gigahorse et voila!


## Does greed work with Vyper contracts?

Yes. Just compile the contract, decompile it with Gigahorse et voila! ;)

## Why my symbolic execution is stuck?!

Symbolic execution is not easy, there are a lot of moving pieces to make this work.
Usually the main reason is there are too many states (i.e., state explosion), or the constraints became so complex that even state-of-the-art solvers cannot do much in solving them.
One of the main strategy to succeed with symbolic execution is to concretize as much as you can and concentrate the symbolic analysis to very well defined tasks.

In other words: hoping to just symbolically execute a contract to enumerate all the vulnerabilities is generally a lost cause.

## I have a problem, how can I get in touch with greed developers?

Just open an [issue](https://github.com/ucsb-seclab/greed/issues) on our GitHub! :)

## How do I know the correspondence between TAC Statement and original opcode?

While this is not always 100% precise, Gigahorse outputs a file called `TAC_Statement_OriginalStatement.csv`. You can find the corresponence between the TAC Statement id and the original PC (bytecode) in there.

## What is the main difference between greed and Mythril?

Mythril is a symbolic analysis tool for the detection of specific classes of vulnerabilities in smart contracts. Converesely, greed is a more flexible smart contract analysis framework that let analysts build any kind of analysis using the high-quality results offered by Gigahorse. Any analysis implemented in Mythril can be built on top of greed, the viceversa is not true.

## What is the main difference between greed and teEther? 

First, teEther is a symbolic executor based on the stack-based EVM opcodes, greed is based on the TAC IR (register-based). Second, we found teEther CFG reconstruction algorithm to be quite outdated when unleashed against modern contracts. Overall, we believe greed offers a more flexible design for building efficient research prototypes.

## What is the main difference between greed and ETHBMC?

Similary to teEther, ETHBMC is based on the stack-based EVM opcodes. Moreover, we found hacking into ETHBMC to be quite cumbersome compared to the Python-based greed APIs. One could argue that ETHBMC is faster than greed (due to its Rust backend), but when comparing the tools against the same conditions, we found this implementation different to be negligable when compared to other issues in symbolic execution.

## Why did you choose to build a symbolic executor on TAC?

We believe register based analyses to be more intuitive and simple to implement. Moreover, Gigahorse gets rid of unnecessary complexity related to the stack-based nature of the EVM that really improve the usability of our tool.
Finally, having a common IR is useful because if the Dedaub team will support a new non-EVM based architecture, we can automatically support it in greed :)
 