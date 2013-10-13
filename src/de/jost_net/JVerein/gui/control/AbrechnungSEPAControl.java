/**********************************************************************
 * $Source$
 * $Revision$
 * $Date$
 * $Author$
 *
 * Copyright (c) by Heiner Jostkleigrewe
 * This program is free software: you can redistribute it and/or modify it under the terms of the 
 * GNU General Public License as published by the Free Software Foundation, either version 3 of the 
 * License, or (at your option) any later version.
 *
 *  This program is distributed in the hope that it will be useful,  but WITHOUT ANY WARRANTY; without 
 *  even the implied warranty of  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See 
 *  the GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License along with this program.  If not, 
 * see <http://www.gnu.org/licenses/>.
 * 
 * heiner@jverein.de
 * www.jverein.de
 **********************************************************************/
package de.jost_net.JVerein.gui.control;

import java.io.File;
import java.io.IOException;
import java.rmi.RemoteException;
import java.text.MessageFormat;
import java.util.Calendar;
import java.util.Date;

import org.eclipse.swt.SWT;
import org.eclipse.swt.widgets.Event;
import org.eclipse.swt.widgets.FileDialog;
import org.eclipse.swt.widgets.Listener;

import de.jost_net.JVerein.Einstellungen;
import de.jost_net.JVerein.DBTools.DBTransaction;
import de.jost_net.JVerein.gui.input.AbbuchungsmodusInput;
import de.jost_net.JVerein.io.AbrechnungSEPA;
import de.jost_net.JVerein.io.AbrechnungSEPAParam;
import de.jost_net.JVerein.keys.Abrechnungsausgabe;
import de.jost_net.JVerein.keys.Abrechnungsmodi;
import de.jost_net.JVerein.util.Dateiname;
import de.jost_net.JVerein.util.JVDateFormatTTMMJJJJ;
import de.willuhn.jameica.gui.AbstractControl;
import de.willuhn.jameica.gui.AbstractView;
import de.willuhn.jameica.gui.Action;
import de.willuhn.jameica.gui.GUI;
import de.willuhn.jameica.gui.input.CheckboxInput;
import de.willuhn.jameica.gui.input.DateInput;
import de.willuhn.jameica.gui.input.SelectInput;
import de.willuhn.jameica.gui.input.TextInput;
import de.willuhn.jameica.gui.parts.Button;
import de.willuhn.jameica.system.Application;
import de.willuhn.jameica.system.BackgroundTask;
import de.willuhn.jameica.system.Settings;
import de.willuhn.logging.Logger;
import de.willuhn.util.ApplicationException;
import de.willuhn.util.ProgressMonitor;

public class AbrechnungSEPAControl extends AbstractControl
{

  private AbbuchungsmodusInput modus;

  private DateInput stichtag = null;

  private DateInput faelligkeit1 = null;

  private DateInput faelligkeit2 = null;

  private DateInput vondatum = null;

  private TextInput zahlungsgrund;

  private CheckboxInput zusatzbetrag;

  private CheckboxInput kursteilnehmer;

  private CheckboxInput kompakteabbuchung;

  private CheckboxInput sepaprint;

  private SelectInput ausgabe;

  private Settings settings = null;

  public AbrechnungSEPAControl(AbstractView view)
  {
    super(view);
    settings = new Settings(this.getClass());
    settings.setStoreWhenRead(true);
  }

  public AbbuchungsmodusInput getAbbuchungsmodus() throws RemoteException
  {
    if (modus != null)
    {
      return modus;
    }
    modus = new AbbuchungsmodusInput(Abrechnungsmodi.KEINBEITRAG);
    modus.addListener(new Listener()
    {
      @Override
      public void handleEvent(Event event)
      {
        Integer m = ((Integer) modus.getValue());
        if (m.intValue() != Abrechnungsmodi.EINGETRETENEMITGLIEDER)
        {
          vondatum.setValue(null);
          vondatum.setEnabled(false);
        }
        else
        {
          vondatum.setEnabled(true);
          vondatum.setValue(new Date());
        }
      }
    });
    return modus;
  }

  public DateInput getStichtag()
  {
    if (stichtag != null)
    {
      return stichtag;
    }
    Date d = null;
    this.stichtag = new DateInput(d, new JVDateFormatTTMMJJJJ());
    this.stichtag.setTitle("Stichtag f�r die Abrechnung");
    this.stichtag.setText("Bitte Stichtag f�r die Abrechnung w�hlen");
    this.stichtag.addListener(new Listener()
    {
      @Override
      public void handleEvent(Event event)
      {
        Date date = (Date) stichtag.getValue();
        if (date == null)
        {
          return;
        }
      }
    });
    this.stichtag.setComment("*)");
    return stichtag;
  }

  public DateInput getFaelligkeit1()
  {
    if (faelligkeit1 != null)
    {
      return faelligkeit1;
    }
    Calendar cal = Calendar.getInstance();
    cal.add(Calendar.DAY_OF_YEAR, 5);
    this.faelligkeit1 = new DateInput(cal.getTime(), new JVDateFormatTTMMJJJJ());
    this.faelligkeit1.setTitle("F�lligkeit SEPA-Lastschrift / Erst+einmalig");
    this.faelligkeit1
        .setText("Bitte F�lligkeitsdatum der SEPA-Lastschrift (Erst+einmalig) w�hlen");
    this.faelligkeit1.addListener(new Listener()
    {
      @Override
      public void handleEvent(Event event)
      {
        Date date = (Date) faelligkeit1.getValue();
        if (date == null)
        {
          return;
        }
      }
    });
    return faelligkeit1;
  }

  public DateInput getFaelligkeit2()
  {
    if (faelligkeit2 != null)
    {
      return faelligkeit2;
    }
    Calendar cal = Calendar.getInstance();
    cal.add(Calendar.DAY_OF_YEAR, 2);
    this.faelligkeit2 = new DateInput(cal.getTime(), new JVDateFormatTTMMJJJJ());
    this.faelligkeit2.setTitle("F�lligkeit SEPA-Lastschrift / Folge");
    this.faelligkeit2
        .setText("Bitte F�lligkeitsdatum der SEPA-Lastschrift (Folge) w�hlen");
    this.faelligkeit2.addListener(new Listener()
    {
      @Override
      public void handleEvent(Event event)
      {
        Date date = (Date) faelligkeit2.getValue();
        if (date == null)
        {
          return;
        }
      }
    });
    return faelligkeit2;
  }

  public DateInput getVondatum()
  {
    if (vondatum != null)
    {
      return vondatum;
    }
    Date d = null;
    this.vondatum = new DateInput(d, new JVDateFormatTTMMJJJJ());
    this.vondatum.setTitle("Anfangsdatum Abrechnung");
    this.vondatum.setText("Bitte Anfangsdatum der Abrechnung w�hlen");
    this.vondatum.setEnabled(false);
    this.vondatum.addListener(new Listener()
    {
      @Override
      public void handleEvent(Event event)
      {
        Date date = (Date) vondatum.getValue();
        if (date == null)
        {
          return;
        }
      }
    });
    return vondatum;
  }

  public TextInput getZahlungsgrund()
  {
    if (zahlungsgrund != null)
    {
      return zahlungsgrund;
    }
    String zgrund = settings.getString("zahlungsgrund", "bitte eingeben");

    zahlungsgrund = new TextInput(zgrund, 50);
    return zahlungsgrund;
  }

  public CheckboxInput getZusatzbetrag()
  {
    if (zusatzbetrag != null)
    {
      return zusatzbetrag;
    }
    zusatzbetrag = new CheckboxInput(settings.getBoolean("zusatzbetraege",
        false));
    return zusatzbetrag;
  }

  public CheckboxInput getKursteilnehmer()
  {
    if (kursteilnehmer != null)
    {
      return kursteilnehmer;
    }
    kursteilnehmer = new CheckboxInput(settings.getBoolean("kursteilnehmer",
        false));
    return kursteilnehmer;
  }

  public CheckboxInput getKompakteAbbuchung()
  {
    if (kompakteabbuchung != null)
    {
      return kompakteabbuchung;
    }
    kompakteabbuchung = new CheckboxInput(settings.getBoolean(
        "kompakteabbuchung", false));
    return kompakteabbuchung;
  }

  public CheckboxInput getSEPAPrint()
  {
    if (sepaprint != null)
    {
      return sepaprint;
    }
    sepaprint = new CheckboxInput(settings.getBoolean("sepaprint", false));
    return sepaprint;
  }

  public SelectInput getAbbuchungsausgabe()
  {
    if (ausgabe != null)
    {
      return ausgabe;
    }
    ausgabe = new SelectInput(Abrechnungsausgabe.getArray(),
        new Abrechnungsausgabe(settings.getInt("abrechnungsausgabe",
            Abrechnungsausgabe.SEPA_DATEI)));
    return ausgabe;
  }

  public Button getStartButton()
  {
    Button button = new Button("starten", new Action()
    {
      @Override
      public void handleAction(Object context)
      {
        try
        {
          doAbrechnung();
        }
        catch (ApplicationException e)
        {
          GUI.getStatusBar().setErrorText(e.getMessage());
        }
        catch (RemoteException e)
        {
          GUI.getStatusBar().setErrorText(e.getMessage());
        }
      }
    }, null, true, "go.png");
    return button;
  }

  private void doAbrechnung() throws ApplicationException, RemoteException
  {
    File sepafile;
    settings.setAttribute("zahlungsgrund", (String) zahlungsgrund.getValue());
    settings.setAttribute("zusatzbetraege", (Boolean) zusatzbetrag.getValue());
    settings
        .setAttribute("kursteilnehmer", (Boolean) kursteilnehmer.getValue());
    settings.setAttribute("kompakteabbuchung",
        (Boolean) kompakteabbuchung.getValue());
    settings.setAttribute("sepaprint", (Boolean) sepaprint.getValue());
    Abrechnungsausgabe aa = (Abrechnungsausgabe) ausgabe.getValue();
    settings.setAttribute("abrechnungsausgabe", aa.getKey());
    Integer modus = null;
    try
    {
      modus = (Integer) getAbbuchungsmodus().getValue();
    }
    catch (RemoteException e)
    {
      throw new ApplicationException(
          "Interner Fehler - kann Abrechnungsmodus nicht auslesen");
    }
    if (faelligkeit1.getValue() == null)
    {
      throw new ApplicationException("F�lligkeitsdatum (Erst/einmalig) fehlt");
    }
    Date f = (Date) faelligkeit1.getValue();
    if (f.before(new Date()))
    {
      throw new ApplicationException(
          "F�lligkeit (Erst/einmalig) muss in der Zukunft liegen");
    }
    if (faelligkeit2.getValue() == null)
    {
      throw new ApplicationException("F�lligkeitsdatum (Folge) fehlt");
    }
    f = (Date) faelligkeit2.getValue();
    if (f.before(new Date()))
    {
      throw new ApplicationException(
          "F�lligkeit (Folge) muss in der Zukunft liegen");
    }
    Date vondatum = null;
    if (stichtag.getValue() == null)
    {
      throw new ApplicationException("Stichtag fehlt");
    }
    if (modus != Abrechnungsmodi.KEINBEITRAG)
    {
      vondatum = (Date) getVondatum().getValue();
      if (modus == Abrechnungsmodi.EINGETRETENEMITGLIEDER && vondatum == null)
      {
        throw new ApplicationException("von-Datum fehlt");
      }
    }
    Integer ausgabe;
    aa = (Abrechnungsausgabe) this.getAbbuchungsausgabe().getValue();
    ausgabe = aa.getKey();

    if (ausgabe == Abrechnungsausgabe.SEPA_DATEI)
    {
      FileDialog fd = new FileDialog(GUI.getShell(), SWT.SAVE);
      fd.setText("SEPA-Ausgabedatei w�hlen.");

      String path = settings.getString("lastdir",
          System.getProperty("user.home"));
      if (path != null && path.length() > 0)
      {
        fd.setFilterPath(path);
      }
      fd.setFileName(new Dateiname("abbuchung", "", Einstellungen
          .getEinstellung().getDateinamenmuster(), "XML").get());
      String file = fd.open();

      if (file == null || file.length() == 0)
      {
        throw new ApplicationException("keine Datei ausgew�hlt!");
      }
      sepafile = new File(file);
    }
    else
    {
      try
      {
        sepafile = File.createTempFile("sepa", null);
      }
      catch (IOException e)
      {
        throw new ApplicationException(
            "Tempor�re Datei f�r die Abbuchung kann nicht erstellt werden.");
      }
    }

    // PDF-Datei f�r Basislastschrift2PDF
    String pdffile = null;
    final Boolean pdfprintb = (Boolean) sepaprint.getValue();
    if (pdfprintb)
    {
      FileDialog fd = new FileDialog(GUI.getShell(), SWT.SAVE);
      fd.setText("PDF-Ausgabedatei w�hlen");

      String path = settings.getString("lastdir",
          System.getProperty("user.home"));
      if (path != null && path.length() > 0)
      {
        fd.setFilterPath(path);
      }
      fd.setFileName(new Dateiname("abbuchung", "", Einstellungen
          .getEinstellung().getDateinamenmuster(), "PDF").get());
      pdffile = fd.open();
    }

    // Wir merken uns noch das Verzeichnis f�rs n�chste mal
    settings.setAttribute("lastdir", sepafile.getParent());
    final AbrechnungSEPAParam abupar;
    try
    {
      abupar = new AbrechnungSEPAParam(this, sepafile, pdffile);
    }
    catch (RemoteException e)
    {
      throw new ApplicationException(e);
    }
    BackgroundTask t = new BackgroundTask()
    {
      @Override
      public void run(ProgressMonitor monitor) throws ApplicationException
      {
        try
        {

          DBTransaction.starten();
          new AbrechnungSEPA(abupar, monitor);
          DBTransaction.commit();

          monitor.setPercentComplete(100);
          monitor.setStatus(ProgressMonitor.STATUS_DONE);
          GUI.getStatusBar().setSuccessText(
              MessageFormat.format(
                  "Abrechnung durchgef�hrt., SEPA-Datei {0} geschrieben.",
                  abupar.sepafile.getAbsolutePath()));
          GUI.getCurrentView().reload();
        }
        catch (ApplicationException ae)
        {
          DBTransaction.rollback();
          monitor.setStatusText(ae.getMessage());
          monitor.setStatus(ProgressMonitor.STATUS_ERROR);
          GUI.getStatusBar().setErrorText(ae.getMessage());
          throw ae;
        }
        catch (Exception e)
        {
          DBTransaction.rollback();
          monitor.setStatus(ProgressMonitor.STATUS_ERROR);
          Logger.error(MessageFormat.format(
              "error while reading objects from {0}",
              abupar.sepafile.getAbsolutePath()), e);
          ApplicationException ae = new ApplicationException(
              MessageFormat.format(
                  "Fehler beim erstellen der Abbuchungsdatei: {0}",
                  abupar.sepafile.getAbsolutePath()), e);
          monitor.setStatusText(ae.getMessage());
          GUI.getStatusBar().setErrorText(ae.getMessage());
          throw ae;
        }
      }

      @Override
      public void interrupt()
      {
        //
      }

      @Override
      public boolean isInterrupted()
      {
        return false;
      }
    };
    Application.getController().start(t);
  }
}
