# Kernel Integration Tests

An integration test for the kernel is composed of two files, one with the `.ck` extension and one with the `.out`
extension. The `.ck` file is the source, which will be run through the kernel and the output compared to the `.out`
file. If the file should succeed type checking,the `.out` file should contain 'success'. Otherwise, the `.out` file
should contain the error message which the kernel is expected to produce.

# TODOs
* Check level defeq for imax
* Check that levels which shouldn't be defeq aren't
* Check that giving the wrong number of level args gives an error
* Check for panics when different parts of a data declaration are not types which should be
* Check deduced types for applications and lambdas
* Check defeq on terms
* Check namespacing (collisions etc.)