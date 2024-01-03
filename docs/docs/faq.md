

# ？FAQ 

## Why is it named greed? 

We all know why people are so interested in finding vulnerabilities in smart contracts..., right? 😉

## How should "greed" be stylized? 

Simple: `greed`, no upper case.

## Why didn't you just implement everything on top of angr?

While implementing everything on top of angr could have been an option, some of the fundamentals of EVM analysis are quite different compared to classic binaries (ARM, x86, AMD64).
Moreover, we wanted to re-use the high-quality analyses (e.g., CFG) and IR offered by Gigahorse. Thus, starting from square one was simpler than fighting with the angr codebase.

## Why did you choose to build a symbolic executor on TAC?

We believe that register-based analyses are more intuitive and straightforward to implement: Gigahorse gets rid of the unnecessary complexity related to the stack-based nature of the EVM, thus really improving the usability of greed.
Having a common intermediate representation is also valuable since, as the Dedaub team adds support for new non-EVM-based architectures, greed will automatically support such architectures. 🙂

## How do I know the correspondence between TAC statements and original opcodes?

While this is not always 100% precise, Gigahorse outputs a file called `TAC_Statement_OriginalStatement.csv`. You can find the correspondence between the TAC Statement ID and the original PC (bytecode) there.

## Does greed support non-EVM contracts?

greed automatically supports anything that Gigahorse supports. Currently, Gigahorse does not support any non-EVM binary. Thus, currently, greed does not support any non-EVM binary.

## Can greed work with contract source code?

Yes. Just compile the contract and decompile it with Gigahorse, et voila!

## Does greed work with Vyper contracts?

Yes. Just compile the contract and decompile it with Gigahorse, et voila! 😉

## What is the main difference between greed and Mythril?

While Mythril is a symbolic analysis tool for detecting specific vulnerabilities in smart contracts, greed is a more flexible analysis framework that lets you build any analysis on top of the high-quality results offered by Gigahorse. Note that any of the analyses in Mythril can be re-implemented on top of greed, but the opposite is not always possible.

## What is the main difference between greed and teEther? 

First, teEther is a symbolic executor built on the stack-based EVM opcodes, but greed builds on the register-based TAC IR. We have also found teEther's CFG reconstruction quite outdated when used against modern contracts. We believe greed offers a more flexible and robust design for building efficient research prototypes.

## What is the main difference between greed and ETHBMC?

Similar to teEther, ETHBMC builds on the stack-based EVM opcodes. We found hacking into ETHBMC quite cumbersome compared to the Python-based greed APIs. One could argue that a Rust backend (ETHBMC) has to be faster than greed (Python), but in our experience, greed offers a more user-friendly Python API **and** better performance – also thanks to some careful optimizations such as our caching layers.

## Why is my symbolic execution stuck?!

Symbolic execution is not easy, and many moving pieces are involved to make this work.
If your script is stuck, it is likely because (1) there are too many states (i.e., state explosion) or (2) the constraints have become so complex that even state-of-the-art solvers cannot do much to solve them.
Two excellent strategies to succeed with symbolic execution are (1) directing the execution by pruning some states and (2) concretizing as many values as possible.

In other words, hoping to "just symbolically execute" a contract and enumerate all vulnerabilities is generally a lost cause.

## I have a problem. How can I get in touch with the greed developers?

Just open an [issue](https://github.com/ucsb-seclab/greed/issues) on our GitHub! 🙂