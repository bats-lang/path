# path

File path manipulation on byte arrays.

## API

- `join(base, child)` — join two path segments with a separator
- `parent(p)` — return the parent directory of a path
- `filename(p)` — return the final component of a path
- `extension(p)` — return the file extension (after the last dot)
- `is_absolute(p)` — test whether a path starts with `/`
- `normalize(p)` — resolve `.` and `..` segments in a path

No I/O — pure path string operations.

## Dependencies

- array
- arith
- str
