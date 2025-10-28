# Auto-Indentation Troubleshooting Guide

## Issue: Line 2 Not Auto-Indenting After `:=`

### Problem Description
When typing `def factorial (n: Nat) : Nat :=` and pressing Enter, line 2 should automatically indent but doesn't.

## Step-by-Step Troubleshooting

### 1. Check Language Detection
- Open `test_indent.lean` in VS Code
- Look at bottom-right corner of VS Code
- Should show "Lean 4" as the language
- If it shows "Plain Text", click it and select "Lean 4"

### 2. Restart Lean Server
- Press `Ctrl/Cmd+Shift+P`
- Type "Lean 4: Restart Server"
- Wait for server to restart
- Try auto-indentation again

### 3. Check VS Code Settings Applied
- Press `Ctrl/Cmd+Shift+P`
- Type "Preferences: Open Settings (JSON)"
- Verify these settings exist:
```json
"editor.autoIndent": "full",
"editor.insertSpaces": true,
"editor.tabSize": 2,
"[lean4]": {
  "editor.autoIndent": "full"
}
```

### 4. Manual Test Procedure
1. Open `test_indent.lean` in VS Code
2. Go to line 1: `def factorial (n: Nat) : Nat :=`
3. Place cursor at the end (after `:=`)
4. Press Enter
5. **Expected**: Cursor should indent 2 spaces
6. **If not working**: Try the solutions below

## Solutions to Try

### Solution 1: Force Reload VS Code
1. Close VS Code completely
2. Reopen VS Code
3. Open the `.lean` file
4. Wait for Lean server to load (check bottom status bar)
5. Try auto-indentation

### Solution 2: Manual Indentation with Tab
If auto-indentation doesn't work:
1. Press Enter after `:=`
2. Press Tab to manually indent
3. Continue typing your code

### Solution 3: Check Extensions
1. Go to Extensions (Ctrl/Cmd+Shift+X)
2. Ensure "Lean 4" extension is installed and enabled
3. Update to latest version if available
4. Restart VS Code

### Solution 4: Use Format Document
1. Write your code without worrying about indentation
2. Press `Shift+Alt+F` (or `Shift+Option+F` on Mac)
3. VS Code will auto-format the entire document

## Alternative Approaches

### Approach 1: Use Template Snippets
Type these snippets and press Tab:
- `def` + Tab → Creates function template with proper indentation
- `match` + Tab → Creates match expression template
- `do` + Tab → Creates do block template

### Approach 2: Copy Working Examples
Use the examples in `indentation_test.lean` as templates:
```lean
def example_function (n : Nat) : Nat :=
  if n = 0 then
    1
  else
    n + 1
```

## Expected Behavior Reference

After pressing Enter, these should auto-indent:
- After `:=` in function definitions
- After `do` keywords  
- After `if`, `then`, `else`
- After `match with`
- After `by` in proofs

## If Nothing Works

### Fallback: Manual Indentation
- Use 2 spaces for each indentation level
- Press Tab to indent, Shift+Tab to outdent
- Use the visual guides to align properly

### Report Issue
If auto-indentation still doesn't work:
1. Check VS Code version: Help → About
2. Check Lean 4 extension version in Extensions panel  
3. Try creating a minimal example file
4. Consider reporting to Lean 4 extension developers

## Current Configuration Status
✅ VS Code settings configured for 2-space indentation
✅ Lean 4 language-specific settings enabled
✅ Custom keybindings for optimal Tab behavior
✅ Test files available for verification