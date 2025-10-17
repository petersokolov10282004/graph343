#!/bin/bash

# Run this script as `./run-full.sh > output.txt 2>&1`

# How we want to call our executable,
# possibly with some command line parameters
EXEC_PROGRAM="./a.out "

# Timestamp for starting this script
date

MACHINE=""
# Display machine name if uname command is available
if hash uname 2>/dev/null; then
  uname -a
  MACHINE=`uname -a`
fi

# Display user name if id command is available
if hash id 2>/dev/null; then
  id
fi


# delete a.out, do not give any errors if it does not exist
rm ./a.out 2>/dev/null

echo "====================================================="
echo "1. Compiles without warnings with -Wall -Wextra flags"
echo "   FIX all warnings if there are any shown below"
echo "====================================================="

g++ -g -Wall -Wextra -Wno-sign-compare *.cpp

echo "====================================================="
echo "2. Runs and produces correct output"
echo "   FIX any issues if the tests below do not pass"
echo "====================================================="

# Execute program
$EXEC_PROGRAM

echo "====================================================="
echo "3. clang-tidy warnings are fixed"
echo "   FIX all warnings if there are any shown below"
echo "====================================================="

if hash clang-tidy 2>/dev/null; then
  clang-tidy *.cpp --
else
  echo "WARNING: clang-tidy not available."
fi

echo "====================================================="
echo "4. Checking formatting using clang-format tool"
echo "   FIX all formatting issues if there are any shown below"
echo "====================================================="

if hash clang-format 2>/dev/null; then
  # different LLVMs have slightly different configurations which can break things, so regenerate
  echo "# generated using: clang-format -style=llvm -dump-config > .clang-format" > .clang-format
  clang-format -style=llvm -dump-config >> .clang-format
  for f in ./*.cpp; do
    echo "Running clang-format on $f"
    clang-format $f | diff $f -
  done
else
  echo "WARNING: clang-format not available"
fi

echo "====================================================="
echo "5. Checking for memory leaks using g++"
echo "   FIX all memory leaks if there are any shown below"
echo "====================================================="

rm ./a.out 2>/dev/null

g++ -fsanitize=address -fno-omit-frame-pointer -g *.cpp
# Execute program
$EXEC_PROGRAM > /dev/null 2> /dev/null


echo "====================================================="
echo "6. Checking for memory leaks using valgrind"
echo "    If you get a message saying \"definitely lost\", fix it"
echo "    If you get a message saying \"All heap blocks were freed -- no leaks are possible\", you are good"
echo "====================================================="

rm ./a.out 2>/dev/null

if hash valgrind 2>/dev/null; then
  g++ -g *.cpp
  # redirect program output to /dev/null will running valgrind
  valgrind --log-file="valgrind-output.txt" $EXEC_PROGRAM > /dev/null 2>/dev/null
  cat valgrind-output.txt
  rm valgrind-output.txt 2>/dev/null
else
  echo "WARNING: valgrind not available"
fi

# Remove the executable
rm -rf ./a.out* 2>/dev/null

date

echo "====================================================="
echo "To create an output.txt file with all the output from this script"
echo "Run the below command"
echo "      ./run-full.sh > output.txt 2>&1 "
echo "====================================================="
