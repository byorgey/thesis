# Got this script from
#
#   http://stackoverflow.com/questions/641427/how-do-i-know-if-pdf-pages-are-color-or-black-and-white
#
# But it doesn't work for me: it just prints 'sRGB' for every page.

#!/bin/bash

FILE=$1
PAGES=$(pdfinfo ${FILE} | grep 'Pages:' | sed 's/Pages:\s*//')

GRAYPAGES=""
COLORPAGES=""

echo "Pages: $PAGES"
N=1
while (test "$N" -le "$PAGES")
do
    COLORSPACE=$( identify -format "%[colorspace]" "$FILE[$((N-1))]" )
    echo "$N: $COLORSPACE"
    if [[ $COLORSPACE == "Gray" ]]
    then
        GRAYPAGES="$GRAYPAGES $N"
    else
        COLORPAGES="$COLORPAGES $N"
    fi
    N=$((N+1))
done

echo "Color pages:"
echo $COLORPAGES
echo "Black-and-white pages:"
echo $GRAYPAGES

#pdftk $FILE cat $COLORPAGES output color_${FILE}.pdf
