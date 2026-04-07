#!/bin/bash

set -e
set -o pipefail

PROJECT_ROOT=""
ORIGINAL_DIR=$PWD
MDNAME="markdown"
output_tex="output.tex"
intermediate_tex="concat.tex"

# Change behaviour if we are running in the command line
cli=false

# Initialize an array
filepaths=()

executables=("katla-pandoc" "xetex" "sed" "pandoc" "latexmk")

for arg in "$@"; do
  case $arg in
    --cli)
      cli=true
      shift # Remove the argument from the list
      ;;
    --project-dir)
      if [ -z "$2" ]; then
        echo "Error: --project-dir requires a filepath argument" >&2
        exit 1
      fi
      PROJECT_ROOT="$2"
      shift 2
      ;;
    *)
      file_name=$arg
      ;;
  esac
done

# Loop through each executable and check if it exists
for cmd in "${executables[@]}"; do
  if ! command -v "$cmd" &> /dev/null; then
    echo "$cmd not found"
    exit 1;
  fi
done


cd $PROJECT_ROOT

# Check if file_name is set (since it's required)
if [ -z "$file_name" ]; then
  echo "Usage: $0 [--cli] <file_name>"
  exit 1
fi

echo "accessing file $PWD/$file_name"

echo "moving to $PROJECT_ROOT"



# Read file line by line into the array
while IFS= read -r line; do
    if [ -f "$line" ]; then
        echo "$line";
        filepaths+=("$line");
    else
        echo "file $PWD/$line does not exists"
        exit 1;
    fi
done < "$ORIGINAL_DIR/$file_name"

cd $ORIGINAL_DIR

rm -rf $output_tex
rm -rf $MDNAME
rm -rf $intermediate_tex
rm -rf output.aux
rm -rf output.log
rm -rf output.out

# Clear the file first
> $MDNAME

# Concatenate each file with newlines in between
for filepath in "${filepaths[@]}"; do
    cat "$PROJECT_ROOT/$filepath" >> $MDNAME
    echo "" >> $MDNAME  # Add a newline
done

pandoc -f markdown+tex_math_dollars+fenced_code_attributes --lua-filter "$ORIGINAL_DIR/tikz.lua" --filter "katla-pandoc" $MDNAME -o $intermediate_tex

cat "$ORIGINAL_DIR/begin" $intermediate_tex "$ORIGINAL_DIR/end" >> $output_tex

latexmk -pdfxe $output_tex

if [ "$cli" = false ]; then
    open output.pdf;
fi

echo word count:
./wordcount.sh $output_tex

# rm -rf $output_tex
rm -rf $MDNAME
rm -rf $intermediate_tex
rm -rf output.aux
rm -rf output.log
rm -rf output.out
rm -rf output.fdb_latexmk
rm -rf output.xdv
rm -rf output.toc

