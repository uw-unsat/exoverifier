#include <gtk/gtk.h>


void on_new1_activate (GtkMenuItem * menuitem, gpointer user_data);

void on_open1_activate (GtkMenuItem * menuitem, gpointer user_data);

void on_save1_activate (GtkMenuItem * menuitem, gpointer user_data);

void on_save_as1_activate (GtkMenuItem * menuitem, gpointer user_data);

void on_quit1_activate (GtkMenuItem * menuitem, gpointer user_data);

void on_cut1_activate (GtkMenuItem * menuitem, gpointer user_data);

void on_copy1_activate (GtkMenuItem * menuitem, gpointer user_data);

void on_paste1_activate (GtkMenuItem * menuitem, gpointer user_data);

void on_delete1_activate (GtkMenuItem * menuitem, gpointer user_data);

void on_about1_activate (GtkMenuItem * menuitem, gpointer user_data);

gboolean
on_main_window_delete_event (GtkWidget * widget,
                             GdkEvent * event, gpointer user_data);

void on_main_window_destroy (GtkObject * object, gpointer user_data);

void on_font1_activate (GtkMenuItem * menuitem, gpointer user_data);

gboolean
on_button_run_button_release_event (GtkWidget * widget,
                                    GdkEventButton * event,
                                    gpointer user_data);

gboolean
on_radiobutton_mode_release_event (GtkWidget * widget,
                                   GdkEventButton * event,
                                   gpointer user_data);

gboolean
on_main_window_delete_event (GtkWidget * widget,
                             GdkEvent * event, gpointer user_data);

void on_go_to_line1_activate (GtkMenuItem * menuitem, gpointer user_data);
