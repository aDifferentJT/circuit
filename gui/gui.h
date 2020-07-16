#ifndef GUI_H
#define GUI_H

#ifdef __cplusplus
extern "C" {
#endif

struct Encoding;

void gui(const char* name, struct Encoding* input, struct Encoding* output);

#ifdef __cplusplus
}
#endif

#endif
