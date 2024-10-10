# fast-smr
    
Toward fast, wait-free, portable, and robust memory reclamation.

### TODOs:
- [ ] relax atomic orderings from SeqCst to Acq/Rel
- [ ] bring back an unsafe variant of wait-free `protect`
- [ ] add docs and update this README
- [ ] add an era counter for platforms without `AtomicU64`