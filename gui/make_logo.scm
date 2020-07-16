(let*
  ((image (car (file-svg-load RUN-NONINTERACTIVE "../logo.svg" "../logo.svg" 300 100 100 1)))
   (drawable (car (gimp-image-get-active-layer image))))
  (file-xpm-save RUN-NONINTERACTIVE image drawable "logo.xpm" "logo.xpm" 64))

(gimp-quit 0)
