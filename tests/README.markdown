This directory contains scripts that test various aspects of Eff:

It uses [cram tests](https://dune.readthedocs.io/en/stable/tests.html#cram-tests),
where each `*.t` file contains the set of shell commands to run together with their
expected output. Files may contain multiple such commands, though we often run just
a single command that loops over all `*.eff` files in a folder.

- Folders `valid` and `invalid` contain basic regression tests, which ensure that
  inferred types and computed values are what we expect. Any time a bug is
  found, one should add a new test that covers it. Folder `valid` contains programs
  that terminate successfuly, while the ones in `invalid` must terminate with an error.

To add new test case, create a test file `text_xyz.eff` in the appropriate folder,
run `dune runtest` to obtain the output, and update the cram file with `dune promote`.

You can also create additional cram files which may source their `*.eff` files from
an existing or a new subfolder.
