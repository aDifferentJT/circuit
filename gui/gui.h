#ifndef GUI_H
#define GUI_H

#ifdef __cplusplus
extern "C" {
#endif

struct Encoding;

void gui(char const *_name, struct Encoding *_input, struct Encoding *_output, int size, int depth);

#ifdef __cplusplus
}
#endif

#endif
