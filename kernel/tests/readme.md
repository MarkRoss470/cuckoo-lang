# Kernel Integration Tests

An integration test for the kernel is composed of two files, one with the `.ck` extension and one with the `.out`
extension. The `.ck` file is the source, which will be run through the kernel and the output compared to the `.out`
file. If the file should succeed type checking,the `.out` file should contain 'success'. Otherwise, the `.out` file
should contain the error message which the kernel is expected to produce.