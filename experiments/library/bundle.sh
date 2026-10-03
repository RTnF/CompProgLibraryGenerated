#!/bin/bash

cd ~/ac2/lib/library
#oj-bundle ./cpp/verify/disjoint_set.test.cpp -I cpp > ./cpp/_bundle/disjoint_set.test.cpp

dirs=$(find ./cpp -maxdepth 1 -type d -not -path "./cpp")
input_dir="./cpp"
output_dir="../library_bundle"

rm -r $output_dir/*

for d in ${dirs[@]}; do
  paths=($d/*)
  mkdir -p "${output_dir}/$d"
  for p in ${paths[@]}; do
    oj-bundle "${p}" -I cpp > "${output_dir}${p#"."}"
  done
done

find $output_dir -type f \( -name "*.cpp" -o -name "*.hpp" \) -exec sed -i '/^#line/d' {} +