# Kernel Integration Tests

An integration test for the kernel is composed of two files, one with the `.ck` extension and one with the `.out`
extension. The `.ck` file is the source, which will be run through the kernel and the output compared to the `.out`
file. If the file should succeed type checking,the `.out` file should contain 'success'. Otherwise, the `.out` file
should contain the error message which the kernel is expected to produce.

Due to the way the tests are collated, the `kernel` crate must be recompiled after adding a new test file for it to be
run. If the output file contains 'REPLACE', the test will overwrite it with the actual error message

# TODOs
* Check that giving the wrong number of level args gives an error
* Check deduced types for applications and lambdas
* Check defeq on terms
* Check namespacing (collisions etc.)