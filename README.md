# Lean Program Verification: Spring Physics Example

A formal verification project demonstrating the use of Lean 4 for mathematical and software verification, starting with classical spring physics as a foundational example.

## 🎯 Project Overview

This repository showcases formal program verification using Lean 4's theorem proving capabilities. It demonstrates how to:

- **Formally define** mathematical concepts (spring force, potential energy)
- **Prove theorems** about physical relationships (F = -dU/dx)
- **Verify computational correctness** through both formal proofs and numerical validation
- **Structure Lean projects** for scientific computing verification

## 🔬 Scientific Background

The project verifies fundamental relationships in spring physics:

- **Hooke's Law**: F(x) = -kx (force proportional to displacement)
- **Potential Energy**: U(x) = (k/2)x² (quadratic energy function)
- **Energy-Force Relationship**: F(x) = -dU/dx (force as negative energy gradient)

## 📁 Project Structure

```
├── RigorousSpringPhysics.lean    # Main verification module with proven theorems
├── Main.lean                     # Demo file showing usage of verified theorems
├── SimpleDemo.lean              # Simple numerical verification without Mathlib
├── SpringPhysics.lean           # Advanced version with full Mathlib (experimental)
├── lakefile.lean               # Lake build configuration
└── README.md                   # This file
```

## 🚀 Quick Start

### Prerequisites

1. **Install Lean 4** and elan (version manager):
   ```bash
   curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
   source ~/.zshrc
   ```

2. **VS Code Setup** (recommended):
   - Install the "Lean 4" extension for syntax highlighting and interactive theorem proving

### Building and Running

```bash
# Clone the repository
git clone https://github.com/mrrahman1517/lean-program-verification.git
cd lean-program-verification/SpringPhysics

# Build the project
lake build

# Run existing programs
lake exe rigorous        # Main verification program
lake exe helloworld     # Hello world example
lake exe test_factorial  # Factorial computation example
```

## 🎮 Running Any Lean File

This project includes several convenient methods to run any Lean file:

### **Method 1: Direct Execution (Simplest)**
```bash
lean --run filename.lean    # Works for any .lean file with main function
```

### **Method 2: Using Helper Scripts**

The project includes several utility scripts to make development easier:

```bash
# Run any existing Lean file
./run_lean.sh filename.lean

# Create a new Lean file from template and run it
./new_lean.sh myprogram    # Creates myprogram.lean and runs it

# Add an existing Lean file as a permanent executable to lakefile.lean
./add_executable.sh myprogram    # Adds myprogram to build system
```

### **Method 3: Manual Lake Configuration**

To permanently add a new executable to the project:

1. Edit `lakefile.lean` and add:
   ```lean
   lean_exe «your_program_name» where
     root := `your_program_name
   ```

2. Build and run:
   ```bash
   lake build your_program_name
   lake exe your_program_name
   ```

### **Creating New Lean Programs**

Any Lean file with a `main` function can be executed. Here's a template:

```lean
def main : IO Unit := do
  IO.println "Hello from Lean!"
  -- Add your code here
```

### **Available Utility Scripts**

- **`run_lean.sh`**: Simple wrapper for `lean --run` with error checking
- **`new_lean.sh`**: Create new Lean file from template and run immediately  
- **`add_executable.sh`**: Add existing file to lakefile for permanent builds
- **`add_and_run.sh`**: Combine adding to lakefile and running (experimental)

## 🎓 Educational Value

This project serves as an educational example of:

### **Formal Verification Concepts**
- Mathematical definitions in type theory
- Theorem proving with tactics
- Computational verification vs formal proof
- Integration of symbolic and numerical methods

### **Lean 4 Features Demonstrated**
- Module system and imports
- Proposition definitions and theorem proving
- Computational functions with Float arithmetic
- Documentation with docstrings
- Project structure with Lake build system

### **Physics and Mathematics**
- Classical mechanics formalization
- Energy and force relationships
- Equilibrium analysis
- Mathematical verification of physical laws

## 🔬 Verification Approach

The project demonstrates two complementary verification strategies:

### **1. Formal Mathematical Proofs**
- Propositions defined for all physical relationships
- Theorems proven using Lean's proof engine
- Type-checked mathematical consistency
- Zero tolerance for logical errors

### **2. Computational Verification**
- Numerical validation at specific test points
- Approximate derivative calculations
- Floating-point arithmetic verification
- Practical confidence building

## 📊 Results

The verification establishes:

- ✅ **Force Definition Correctness**: F(x) = -kx is properly implemented
- ✅ **Energy Definition Correctness**: U(x) = (k/2)x² is properly implemented  
- ✅ **Equilibrium Properties**: Both F(0) = 0 and U(0) = 0 are proven
- ✅ **Numerical Verification**: F = -dU/dx relationship confirmed computationally
- ✅ **Linearity Properties**: Force linearity and energy scaling proven (with axioms)

Sample output:
```
Spring Physics Verification (Symbolic)
=======================================
✓ Proved: F(x) = -kx
✓ Proved: U(x) = (k/2)x²  
✓ Proved: F(x) = -dU/dx (symbolically)
✓ Proved: Equilibrium properties
✓ Proved: Linearity properties

Examples with exact rational arithmetic:
• F(2, 3) = -6 (verified)
• U(2, 3) = 9 (verified)
• F(1, -2) = 2 (verified)
```

## 🛠️ Technical Details

### **Lean 4 Version**: 4.25.0-rc2
### **Build System**: Lake
### **Dependencies**: Minimal (basic Lean 4 standard library)

### **Key Files**:
- **RigorousSpringPhysics.lean**: Core verification with formal theorems
- **Main.lean**: Demonstration of theorem usage
- **SimpleDemo.lean**: Lightweight numerical verification

## 🔮 Future Directions

This foundational example can be extended to:

### **Physics Expansions**
- Harmonic oscillator dynamics
- Conservation laws (energy, momentum)
- Multi-body systems
- Electromagnetic field theory

### **Software Verification**
- Algorithm correctness proofs
- Data structure verification
- Concurrency verification
- Cryptographic protocol verification

### **Advanced Mathematics**
- Differential equations
- Linear algebra verification
- Numerical analysis correctness
- Statistical methods verification

## 🤝 Contributing

This project welcomes contributions! Areas of interest:

1. **New Physics Domains**: Expand to other areas of physics
2. **Advanced Theorems**: More sophisticated mathematical proofs
3. **Educational Materials**: Tutorials and explanations
4. **Performance**: Optimization of proof checking
5. **Integration**: Connection with other verification tools

## 📚 Learning Resources

- [Lean 4 Manual](https://lean-lang.org/lean4/doc/)
- [Mathematics in Lean](https://leanprover-community.github.io/mathematics_in_lean/)
- [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/)
- [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/)

## 📄 License

MIT License - see LICENSE file for details.

## 👤 Author

**Muntasir Rahman** - [mrrahman1517](https://github.com/mrrahman1517)

Part of ongoing research in formal verification and mathematical software development.

---

*This project demonstrates that formal verification is not just theoretical—it's a practical tool for ensuring correctness in scientific computing and software development.*