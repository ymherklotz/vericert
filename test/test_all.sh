mytmpdir=$(mktemp -d 2>/dev/null || mktemp -d -t 'mytmpdir')
echo "--------------------------------------------------"
echo "Created working directory: $mytmpdir"
echo "--------------------------------------------------"

if [[ -z $1 ]]; then
    test_dir=.
else
    test_dir=$1
fi

test_command() {
    local loc=$(command -v $1)
    if [[ $? -eq 0  ]]; then
        echo "Found $1: $loc"
    else
        echo "Could not find $1"
        exit 1
    fi
}

test_command iverilog
test_command gcc

echo "--------------------------------------------------"

for cfile in $test_dir/*.c; do
    echo "Testing $cfile"
    outbase=$mytmpdir/$(basename $cfile)
    gcc -o $outbase.gcc $cfile >/dev/null 2>&1
    $outbase.gcc
    expected=$?
    ./bin/vericert -drtl -o $outbase.v $cfile >/dev/null 2>&1
    if [[ ! -f $outbase.v ]]; then
        echo "ERROR"
        continue
    fi
    iverilog -o $outbase.iverilog $outbase.v
    actual=$($outbase.iverilog | sed -E -e 's/[^0-9]+([0-9]+)/\1/')
    if [[ $expected = $actual ]]; then
        echo "OK"
    else
        echo "FAILED: $expected != $actual"
    fi
done

echo "--------------------------------------------------"

rm -rf $mytmpdir
