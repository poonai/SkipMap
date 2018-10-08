# Concurrent SkipMap

Thread safe insert only concurrent skipmap.

All the reference movement of the nodes are done through atomic instruction.

# Notes

- No Update
- No Delete
- Used features `allocator_api`, `rustc_private`

# Benchmarks

```
test insert            ... bench:   2,187,023 ns/iter (+/- 70,591)
test insert_concurrent ... bench:   1,494,069 ns/iter (+/- 164,952)

```

# Reference

- badger (go key value database, which is of RocksDB)
- https://gitlab.com/boats/skiplist/tree/master/src/skiplis