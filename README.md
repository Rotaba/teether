# teEther

## Quickstart
The start point for analysis is `combined_call_exploit.py`
You invoke it as 
```bash
python combined_call_exploit.py <contract-code-file> <attacker address> <target-amount>
```
where
    * `<contract-code-file>` is a hex-encoded contract
    * `<attacker address>` is the address assumed under attack control
    * `<target-amount>` is a specification of how many wei to leak. It can take three forms
        + `+1000` for "at least 1000 wei" (default)
        + `=1000` for "exactly 1000 wei"
        + `-1000` for "at most 1000 wei"

## Repository Structure

### `ethanalyze`
Contains the teEther core:
    * `cfg.py`: control flow graph representation
    * `cfg_back_traversal.py`: backwards taint tracking
    * `constraints.py`: constraint solving and utility functions
    * `diassembly.py`: raw bytecode disassembly
    * `evm.py`: contains two VMs, one for concrete execution (`run`), and one for symbolic execution (`run_symbolic`)
    * `explorer.py`: Forwards CFG exploration
    * `frontierset.py`: Special data-structure to handle dependent edges during CFG traversal
    * `intrange.py`: Representation of integer ranges, including boolean functions on integer ranges
    * `memory.py`: Abstraction for symbolic memory
    * `opcodes.py`: EVM opcode definitions
    * `project.py`: Main interface to teEther
    * `slicing.py`: backwards slicing
    * `utils.py`: utility functions
    * `z3_extra_utils.py`: Z3 specific utility functions

### `unittests`
Unittests. Requires [test](https://projects.cispa.saarland/krupp/teether-test/) repository.

### Main directory
A bunch of scripts. Most notably:
    * `asm.py`: Small assembler. Converts `.asm` files to bytecode
    * `combined_call_exploit.py`: multistate exploits
    * `extract_contract_code.py`: Extract final contract code from constructor code (as given by `solc --bin`)
    * `plot_cfg.py`: Generate `.dot` graphs from bytecode
    * `sig.py`: Compute 4 byte signature from Solidity function signature
