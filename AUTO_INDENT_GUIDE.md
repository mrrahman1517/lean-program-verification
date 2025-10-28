# Auto-Indentation Test Guide

## ✅ Fixed Configuration

The issue was that Lean 4 requires **spaces instead of tabs**. The configuration has been updated to:
- Use 2 spaces for indentation (visually appears like tabs)
- Auto-indent based on code structure
- Tab key inserts proper indentation

## How to Test Auto-Indentation in VS Code

### 1. Test After 'do' Keywords
1. Open `indentation_test.lean` in VS Code
2. Go to the end of line 27: `def test : IO Unit := do`
3. Press **Enter**
4. **Expected**: Cursor should auto-indent with 2 spaces
5. Type: `let y := 10`
6. Press **Enter** again
7. **Expected**: Should maintain same indentation level

### 2. Test Nested Indentation
Try typing this structure:
```lean
def nested_example : IO Unit := do
  -- Press Enter after 'do' - should auto-indent
  if true then
    -- Press Enter after 'then' - should indent further
    IO.println "true case"
  else
    -- Should align with 'if'
    IO.println "false case"
```

### 3. Test Match Expression
```lean
def test_match (n : Nat) : String :=
  match n with
  -- Press Enter after 'with' - should auto-indent
  | 0 => "zero"
  -- Press Enter - should align with previous '|'
  | 1 => "one"
  | _ => "other"
```

## Current Settings

- **Indentation**: 2 spaces (not tab characters)
- **Tab key behavior**: Inserts proper indentation
- **Auto-indent**: Enabled for code structure
- **Visual width**: 2 spaces per indent level

## Troubleshooting

If auto-indentation still doesn't work:

1. **Restart VS Code** after the configuration changes
2. **Check the language mode** - ensure file is recognized as "Lean 4"
3. **Try Ctrl/Cmd+Shift+P** → "Lean 4: Restart Server"
4. **Manual indentation**: Use Tab/Shift+Tab if auto-indent fails

## Expected Behavior

- **After `do`**: Next line indented with 2 spaces
- **After `if/then/else`**: Proper nested indentation
- **After `match with`**: Indentation for pattern matching
- **After `by`**: Indentation for proof tactics
- **Tab key**: Increases indentation by 2 spaces
- **Shift+Tab**: Decreases indentation by 2 spaces

## Visual Confirmation

With `"editor.renderWhitespace": "boundary"` enabled, you should see:
- Dots for spaces at word boundaries
- Indentation guides (vertical lines)
- Consistent 2-space indentation levels